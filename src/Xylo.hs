{-# LANGUAGE MultiParamTypeClasses, Rank2Types #-}

module Xylo where

import Control.Applicative ((<*>), (<$>))
import Control.Category
import Prelude hiding (takeWhile, (++), zip, id, (.))
import qualified Data.DList as L
import Data.DList (DList)
import Data.Function (fix)
import Data.Maybe (isJust)

data SF a b = Emit b (SF a b)
            | Receive (a -> SF a b)
            | Stop

data SF2 a b c =
    Emit2 c (SF2 a b c)
  | ReceiveL (a -> SF2 a b c)
  | ReceiveR (b -> SF2 a b c)
  | Stop2

instance Category SF where
  id = arr id
  (Emit a as) . sf = Emit a (as . sf)
  (Receive f) . (Emit b bs) = f b . bs
  sf . (Receive g) = Receive (\a -> sf . g a)
  _ . Stop = Stop
  Stop . _ = Stop

arr :: (a -> b) -> SF a b
arr f = z where
  loop a = Emit (f a) z
  z = Receive loop

fromList :: [a] -> SF x a
fromList [] = Stop
fromList (h:t) = Emit h (fromList t)

prepend :: [a] -> SF a a
prepend [] = arr id
prepend (h:t) = Emit h (prepend t)

buffer :: Int -> SF a [a]
buffer n = z
  where
    z = loop n L.empty
    loop 0 acc = Emit (L.toList acc) z
    loop x acc = Receive $ \a -> loop (x - 1) (L.snoc acc a)

unbuffer :: SF [a] a
unbuffer = z
  where loop []     = z
        loop (x:xs) = Emit x $ loop xs
        z = Receive loop

filter :: (a -> Bool) -> SF a a
filter p = z
  where loop a | p a = Emit a z
               | otherwise = z
        z = Receive loop

drop :: Int -> SF a a
drop n = Receive $ loop n
  where loop 0 a = Emit a . Receive $ loop 0
        loop x a = Receive . loop $ x - 1

take :: Int -> SF a a
take n = Receive $ loop n
  where loop 0 a = Stop
        loop x a = Emit a . Receive . loop $ x - 1

takeWhile :: (a -> Bool) -> SF a a
takeWhile p = z
  where loop a | p a = Emit a z
               | otherwise = Stop
        z = Receive loop

untilNothing :: SF (Maybe a) a
untilNothing = z
  where go Nothing = Stop
        go (Just a) = Emit a z
        z = Receive go

chunkBy :: Ord k => (a -> k) -> SF a ([a],k)
chunkBy = undefined

chunk :: Ord k => SF (a, k) [(a,k)]
chunk = Receive wff
  where wff (a, k) = Receive (acc k L.empty)
        acc ck xs x@(a, k) | ck == k = Receive $ acc ck (L.snoc xs x)
                           | otherwise = Emit (L.toList xs) (Receive wff)

(***) :: SF a a2 -> SF b b2 -> SF2 a2 b2 c -> SF2 a b c
(***) a b (Emit2 c sf) = Emit2 c $ (a *** b) sf
(***) (Emit a sf) b (ReceiveL f) = (sf *** b) (f a)
(***) (Receive g) b (ReceiveL f) = ReceiveL (\a -> ((g a) *** b) (ReceiveL f))
(***) Stop b (ReceiveL f) = Stop2
(***) a (Emit b sf) (ReceiveR f) = (a *** sf) (f b)
(***) a (Receive g) (ReceiveR f) = ReceiveR (\b -> (a *** (g b)) (ReceiveR f))
(***) _ _ _ = Stop2

(||>) :: SF2 a b c -> SF c d -> SF2 a b d
s ||> Emit d t = Emit2 d (s ||> t)
Emit2 c s ||> Receive f = s ||> f c
ReceiveL g ||> x = ReceiveL (\a -> g a ||> x)
ReceiveR g ||> x = ReceiveR (\b -> g b ||> x)
_ ||> _ = Stop2

passL :: SF2 a b a
passL = liftL (arr id)

passR :: SF2 a b b
passR = liftR (arr id)

liftL :: SF a b -> SF2 a c b
liftL (Receive f) = ReceiveL (liftL . f)
liftL (Emit b sf) = Emit2 b (liftL sf)
liftL Stop = Stop2

liftR :: SF a b -> SF2 c a b
liftR (Receive f) = ReceiveR (liftR . f)
liftR (Emit a sf) = Emit2 a (liftR sf)
liftR Stop = Stop2

mergeOuter :: Ord k => SF2 (Maybe ([a], k)) (Maybe ([b], k)) (These a b)
mergeOuter = ReceiveL (\aks -> ReceiveR (\bks ->
  case (aks, bks) of
    (Nothing, Nothing) -> Stop2
    (Just as, Nothing) -> passL ||> unMaybe This ||> prepend (map This $ fst as)
    (Nothing, Just bs) -> passR ||> unMaybe That ||> prepend (map That $ fst bs)
    (Just (as, k1), Just (bs, k2))
      | k1 == k2 -> mergeOuter ||> prepend (These <$> as <*> bs)
      | k1 < k2 -> mergeOuter ||> prepend (map This as)
      | otherwise -> mergeOuter ||> prepend (map That bs)))
  where
    unMaybe :: (a -> b) -> SF (Maybe ([a],k)) b
    unMaybe f = arr (\o -> (map f . fst) <$> o) >>> untilNothing >>> unbuffer

mojoin :: Ord k => SF2 (Maybe (a,k)) (Maybe (b,k)) (These a b)
mojoin = undefined -- (chunkBy (fst <$>) *** chunkBy (fst <$>)) $ mergeOuter

data These a b = This a | That b | These a b

fromMaybes :: Maybe a -> Maybe b -> These a b
fromMaybes (Just a) (Just b) = These a b
fromMaybes (Just a) Nothing = This a
fromMaybes Nothing (Just b) = That b
fromMaybes _ _ = error "fromMaybes Nothing Nothing"

infixl 9 |>
infixl 8 ++

(|>) :: Stream f => f a -> SF a b -> f b
s |> f = transform f s

class Stream f where

  empty :: f a

  transform :: SF a b -> f a -> f b

  align :: SF2 a b c -> f a -> f b -> f c

  (++) :: f a -> f a -> f a

  apply :: f (a -> b) -> f a -> f b
  apply f a = zip f a |> arr (uncurry ($))

  -- concat :: (forall u . f t (f u a)) -> f t a
  -- interleave :: f (f a) -> f a

  literal :: [a] -> f a
  literal as = empty |> fromList as

  pure :: a -> f a
  pure a = literal (fix (a:))

  zip :: f a -> f b -> f (a,b)
  zip = align (fix $ \self -> ReceiveL (\a -> ReceiveR (\b -> Emit2 (a,b) self)))

  zipAll :: f a -> f b -> f (These a b)
  zipAll a b =
       zip (terminated a) (terminated b)
    |> takeWhile (\(a,b) -> isJust a || isJust b)
    |> arr (uncurry fromMaybes)

  terminated :: f a -> f (Maybe a)
  terminated a = (a |> arr Just ++ pure Nothing)

