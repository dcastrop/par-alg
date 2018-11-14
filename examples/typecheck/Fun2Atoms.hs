module Fun2Atoms where

import AlgPrelude

split :: [Int] -> Sum2 (Sum2 () Int) (Pair2 [Int] [Int])
split [] = Inj0_2 (Inj0_2 ())
split [x] = Inj0_2 (Inj1_2 x)
split l   = Inj1_2 $ go l [] []
  where
    go [] l r = Pair2 l r
    go (x:xs) l r = go xs r (x : l)

merge :: Sum2 (Sum2 () Int) (Pair2 [Int] [Int]) -> [Int]
merge (Inj0_2 (Inj0_2 _)) = []
merge (Inj0_2 (Inj1_2 x)) = [x]
merge (Inj1_2 (Pair2 l r)) = go l r
  where
    go l1@(h1 : t1) l2@(h2 : t2)
      | h1 <= h2 = h1 : go t1 l2
      | otherwise = h2 : go l1 t2
    go l1 l2 = l1 ++ l2

