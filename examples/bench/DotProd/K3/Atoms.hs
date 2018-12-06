{-# LANGUAGE DeriveGeneric #-}
module Atoms where

import Control.DeepSeq
import GHC.Generics (Generic, Generic1)

import qualified Data.Vector as V

import AlgPrelude

type L1 a = Sum2 () (Pair2 Integer a)
type L2 a = Sum2 () (Pair2 (Pair2 Integer Integer) a)
type P a = Sum2 (Sum2 () (Pair2 Integer Integer)) (Pair2 a a)

type RecL1 = V.Vector Integer

inL1 (Inj0_2 v0) = V.empty
inL1 (Inj1_2 (Pair2 v0 v1)) = V.cons v0 v1

outL1 v0
  | V.null v0 = Inj0_2 ()
  | otherwise = Inj1_2 (Pair2 (V.head v0) (V.tail v0))

toL1 = V.fromList

type RecL2 = V.Vector (Pair2 Integer Integer)

fromL2 = V.toList

toL2 = V.fromList

inL2 = inL1

outL2 = outL1

data RecP
  = PInj0_2 (Sum2 () (Pair2 Integer Integer))
  | PInj1_2 RecP RecP

inP (Inj0_2 v0) = PInj0_2 v0
inP (Inj1_2 (Pair2 v0 v1)) = PInj1_2 v0 v1

outP (PInj0_2 v0) = Inj0_2 v0
outP (PInj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)

imult :: Pair2 Integer Integer -> Integer
imult (Pair2 i j) = i * j

isum :: Pair2 Integer Integer -> Integer
isum (Pair2 i j) = i + j

type PL1 = Pair2 RecL1 RecL1

split :: PL1 -> Pair2 PL1 PL1
split (Pair2 v1 v2) = Pair2 (Pair2 v11 v21) (Pair2 v12 v22)
  where
    (v11, v12) = split v1
    (v21, v22) = split v2
    split v
      | V.null v = (v, v)
      | otherwise = V.splitAt n v
      where
        n = V.length v `div` 2
