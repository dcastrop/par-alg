module Atoms where

import AlgPrelude

type LInt = [Int]

split :: LInt -> Sum2 (Sum2 () Int) (Pair2 LInt LInt)
split []  = Inj0_2 (Inj0_2 ())
split [x] = Inj0_2 (Inj1_2 x)
split (x:y:xs) = Inj1_2 $ go [x] [y] xs
  where
    go l r [] = Pair2 l r
    go l r (x : xs) = go r (x : l) xs

merge :: Sum2 (Sum2 () Int) (Pair2 LInt LInt) -> LInt
merge (Inj0_2 (Inj0_2 _)) = []
merge (Inj0_2 (Inj1_2 x)) = [x]
merge (Inj1_2 (Pair2 l r)) = go l r
  where
    go xs ys = case (xs, ys) of
      ([], _) -> ys
      (_, []) -> xs
      (x:xt, y:yt) -> if x < y
        then x : go xt ys
        else y : go xs yt


