module MergesortAtoms where

import AlgPrelude
import Data.Vector ( Vector )
import qualified Data.Vector as V

type VInt = Vector Int

split :: Vector Int -> Sum2 (Sum2 () Int) (Pair2 (Vector Int) (Vector Int))
split l
  | len == 0  = Inj0_2 (Inj0_2 ())
  | len == 1  = Inj0_2 (Inj1_2 $! V.head l)
  | otherwise = Inj1_2 $ Pair2 ll lr
  where
    (ll, lr) = V.splitAt hlen l
    len = V.length l
    hlen = len `div` 2

merge :: Sum2 (Sum2 () Int) (Pair2 VInt VInt) -> VInt
merge (Inj0_2 (Inj0_2 _)) = V.empty
merge (Inj0_2 (Inj1_2 x)) = V.singleton x
merge (Inj1_2 (Pair2 l r)) = go l r
  where
    go xs ys = case (xs V.!? 0, ys V.!? 0) of
      (Nothing, _) -> ys
      (_, Nothing) -> xs
      (Just x, Just y) -> if x < y
        then x `V.cons` go (V.tail xs) ys
        else y `V.cons` go xs (V.tail ys)


