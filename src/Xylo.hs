{-# LANGUAGE MultiParamTypeClasses, Rank2Types, GADTs, PolyKinds, DataKinds, KindSignatures, FlexibleInstances #-}

module Xylo where

import Control.Monad (join)
import Control.Applicative ((<*>), (<$>), Applicative)
import Control.Category
import Prelude hiding (takeWhile, (++), zip, id, (.))
import qualified Data.DList as L
import Data.DList (DList)
import Data.Function (fix)
import Data.Maybe (isJust)

data SF k a b = Emit b (SF k a b)
              | Receive (k a (SF k a b))

data Product a b = Pair a b

data Fork :: Product * * -> * -> * where
  L :: (a -> c) -> Fork (Pair a b) c
  R :: (b -> c) -> Fork (Pair a b) c

data NDFork :: Product * * -> * -> * where
  NDL :: (a -> c) -> NDFork (Pair a b) c
  NDR :: (b -> c) -> NDFork (Pair a b) c
  NDB :: (a -> c) -> (b -> c) -> NDFork (Pair a b) c

type SF1 = SF (->)
type SF2 a b = SF Fork (Pair a b)

instance Category (SF (->)) where
  id = arr id
  Emit a as . sf = Emit a (as . sf)
  Receive f . Emit b bs = f b . bs
  sf . Receive g = Receive (\a -> sf . g a)

arr :: (a -> b) -> SF1 a b
arr f = z where
  loop a = Emit (f a) z
  z = Receive loop

forever :: b -> SF k a b
forever b = Emit b z
  where z = forever b

stop :: SF k a (Maybe b)
stop = forever Nothing

fromList :: [a] -> SF k x (Maybe a)
fromList [] = stop
fromList (h:t) = Emit (Just h) (fromList t)

prepend :: [a] -> SF1 a a
prepend [] = arr id
prepend (h:t) = Emit h (prepend t)

buffer :: Int -> SF1 a [a]
buffer n = z
  where
    z = loop n L.empty
    loop 0 acc = Emit (L.toList acc) z
    loop x acc = Receive $ \a -> loop (x - 1) (L.snoc acc a)

unbuffer :: SF1 [a] a
unbuffer = z
  where loop []     = z
        loop (x:xs) = Emit x $ loop xs
        z = Receive loop

liftMaybe :: SF1 a b -> SF1 (Maybe a) (Maybe b)
liftMaybe (Emit h t) = Emit (Just h) (liftMaybe t)
liftMaybe (Receive g) = Receive go
  where
    go Nothing = Emit Nothing (Receive go)
    go (Just a) = liftMaybe (g a)

liftMaybe2 :: SF2 a b c -> SF2 (Maybe a) (Maybe b) (Maybe c)
liftMaybe2 (Emit a as) = Emit (Just a) (liftMaybe2 as)
liftMaybe2 (Receive (L f)) = Receive (L go)
  where
    go Nothing = Emit Nothing (Receive (L go))
    go (Just a) = liftMaybe2 (f a)
liftMaybe2 (Receive (R f)) = Receive (R go)
  where
    go Nothing = Emit Nothing (Receive (R go))
    go (Just a) = liftMaybe2 (f a)

filter :: (a -> Bool) -> SF1 a a
filter p = z
  where loop a | p a = Emit a z
               | otherwise = z
        z = Receive loop

drop :: Int -> SF1 a a
drop n = Receive $ loop n
  where loop 0 a = Emit a . Receive $ loop 0
        loop x a = Receive . loop $ x - 1

take :: Int -> SF1 a (Maybe a)
take n = Receive $ loop n
  where loop 0 a = stop
        loop x a = Emit (Just a) . Receive . loop $ x - 1

takeWhile :: (a -> Bool) -> SF1 a (Maybe a)
takeWhile p = z
  where loop a | p a = Emit (Just a) z
               | otherwise = stop
        z = Receive loop

untilNothing :: SF1 (Maybe a) (Maybe a)
untilNothing = takeWhile isJust >>> arr join

chunkBy :: Ord k => (a -> k) -> SF1 (Maybe a) (Maybe ([a], k))
chunkBy f = Receive wff
  where wff Nothing  = stop
        wff (Just a) = Receive (acc (f a) (L.singleton a))
        acc ck as (Just a) | ck == (f a) = Receive $ acc ck (L.snoc as a)
                           | otherwise = Emit (Just (L.toList as, ck)) (wff (Just a))
        acc ck as Nothing = Emit (Just (L.toList as, ck)) stop

chunk :: Ord k => SF1 (Maybe (a, k)) (Maybe ([a], k))
chunk = chunkBy snd >>> arr (fmap (\(aks, k) -> (map fst aks, k)))

(***) :: SF1 a a2 -> SF1 b b2 -> SF2 a2 b2 c -> SF2 a b c
(***) a b (Emit c sf) = Emit c $ (a *** b) sf
(***) (Emit a sf) b (Receive (L f)) = (sf *** b) (f a)
(***) (Receive g) b (Receive (L f)) = Receive (L (\a -> ((g a) *** b) (Receive (L f))))
(***) a (Emit b sf) (Receive (R f)) = (a *** sf) (f b)
(***) a (Receive g) (Receive (R f)) = Receive (R (\b -> (a *** (g b)) (Receive (R f))))

(||>) :: SF2 a b c -> SF1 c d -> SF2 a b d
s ||> Emit d t = Emit d (s ||> t)
Emit c s ||> Receive f = s ||> f c
Receive (L g) ||> x = Receive (L (\a -> g a ||> x))
Receive (R g) ||> x = Receive (R (\b -> g b ||> x))

passL :: SF2 a b a
passL = liftL (arr id)

passR :: SF2 a b b
passR = liftR (arr id)

liftL :: SF1 a b -> SF2 a c b
liftL (Receive f) = Receive (L (liftL . f))
liftL (Emit b sf) = Emit b (liftL sf)

liftR :: SF1 a b -> SF2 c a b
liftR (Receive f) = Receive (R (liftR . f))
liftR (Emit a sf) = Emit a (liftR sf)

mergeOuter :: Ord k => SF2 (Maybe ([a], k)) (Maybe ([b], k)) (Maybe (These a b))
mergeOuter = Receive (L (\aks -> Receive (R (\bks ->
  case (aks, bks) of
    (Nothing, Nothing) -> stop
    (Just as, Nothing) -> passL
                      ||> unMaybe This
                      ||> prepend (map (Just . This) $ fst as)
    (Nothing, Just bs) -> passR
                      ||> unMaybe That
                      ||> prepend (map (Just . That) $ fst bs)
    (Just (as, k1), Just (bs, k2))
      | k1 == k2 -> mergeOuter ||> prepend (Just <$> (These <$> as <*> bs))
      | k1 < k2 -> mergeOuter ||> prepend (map (Just . This) as)
      | otherwise -> mergeOuter ||> prepend (map (Just . That) bs)))))
  where
    unMaybe :: (a -> b) -> SF1 (Maybe ([a],k)) (Maybe b)
    unMaybe f = arr (\o -> (map f . fst) <$> o) >>> liftMaybe unbuffer

mojoin :: Ord k => (a -> k) -> (b -> k) -> SF2 (Maybe a) (Maybe b) (Maybe (These a b))
mojoin l r = (z l *** z r) mergeOuter where
  f g Nothing = Nothing
  f g (Just a)  = Just (a, g a)
  z g = chunk . (arr $ f g)

data These a b = This a | That b | These a b

fromMaybes :: Maybe a -> Maybe b -> These a b
fromMaybes (Just a) (Just b) = These a b
fromMaybes (Just a) Nothing = This a
fromMaybes Nothing (Just b) = That b
fromMaybes _ _ = error "fromMaybes Nothing Nothing"

infixl 9 |>
infixl 8 ++

(|>) :: Stream f => f a -> SF1 a b -> f b
s |> f = transform f s

class Stream f where

  empty :: f a

  transform :: SF1 a b -> f a -> f b

  align :: SF2 a b c -> f a -> f b -> f c

  (++) :: f a -> f a -> f a

  apply :: f (a -> b) -> f a -> f b
  apply f a = zip f a |> arr (uncurry ($))

  trim :: f (Maybe a) -> f a

  literal :: [a] -> f a
  literal as = trim $ empty |> fromList as

  pure :: a -> f a
  pure a = literal (fix (a:))

  zip :: f a -> f b -> f (a,b)
  zip = align (fix $ \self -> Receive (L (\a -> Receive (R (\b -> Emit (a,b) self)))))

  zipAll :: f a -> f b -> f (These a b)
  zipAll a b = trim (
       zip (terminated a) (terminated b)
    |> takeWhile (\(a,b) -> isJust a || isJust b))
    |> arr (uncurry fromMaybes)

  terminated :: f a -> f (Maybe a)
  terminated a = (a |> arr Just ++ pure Nothing)

  joinAll :: Ord k => (a -> k) -> (b -> k) -> f a -> f b -> f (These a b)
  joinAll f g a b = trim $ align (mojoin f g) (terminated a) (terminated b)

data Resource a where
  FileLines :: String -> Resource String
  Pipe :: Resource a -> SF1 a b -> Resource b
  -- Align :: Resource a -> Resource b -> Resource
  --

-- instance Stream Resource where

-- class Stream f => StreamIO f where
--   concat :: f (Resource a) -> f a
  -- interleave :: f (f a) -> f a

