module Atoms where

import Data.Complex
import AlgPrelude

type RecL = [Complex Float]

inL :: Sum2 () (Pair2 (Complex Float) RecL) -> RecL
inL (Inj0_2 _) = []
inL (Inj1_2 (Pair2 x y)) = x : y

fl :: Pair2 RecL RecL -> RecL
fl (Pair2 xs ys) = zipWith (+) xs ys

fr :: Pair2 RecL RecL -> RecL
fr (Pair2 xs ys) = zipWith (-) xs ys

fo :: RecL -> RecL
fo x = zipWith (\z k -> exp' k * z) x [0..]
  where
    exp' k = cis $ -2 * pi * fromIntegral k / fromIntegral n
    n = length x * 2


deinterleave :: RecL -> Sum2 (Sum2 () (Complex Float)) (Pair2 RecL RecL)
deinterleave [] = Inj0_2 (Inj0_2 ())
deinterleave [x] = Inj0_2 (Inj1_2 x)
deinterleave (x:y:zs) = Inj1_2 $! go [x] [y] zs
  where
    go l r []  = Pair2 (reverse l) (reverse r)
    go l r [_] = Pair2 (reverse l) (reverse r)
    go l r (a:b:cs) = go (a:l) (b:r) cs

app :: Pair2 RecL RecL -> RecL
app (Pair2 xs ys) = xs ++ ys
