module Atoms where

import AlgPrelude


type L1 a = Sum2 () (Pair2 Int a)
type L2 a = Sum2 () (Pair2 (Pair2 Int Int) a)

data RecL1
  = L1Inj0_2 ()
  | L1Inj1_2 Int RecL1

inL1 (Inj0_2 v0) = L1Inj0_2 v0
inL1 (Inj1_2 (Pair2 v0 v1)) = L1Inj1_2 v0 v1

outL1 (L1Inj0_2 v0) = Inj0_2 v0
outL1 (L1Inj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)

data RecL2
  = L2Inj0_2 ()
  | L2Inj1_2 (Pair2 Int Int) RecL2

inL2 (Inj0_2 v0) = L2Inj0_2 v0
inL2 (Inj1_2 (Pair2 v0 v1)) = L2Inj1_2 v0 v1

outL2 (L2Inj0_2 v0) = Inj0_2 v0
outL2 (L2Inj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)


imult :: Pair2 Int Int-> Int
imult (Pair2 i j) = i * j

isum :: Pair2 Int Int-> Int
isum (Pair2 i j) = i + j

