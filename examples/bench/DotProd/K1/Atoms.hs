{-# LANGUAGE DeriveGeneric #-}
module Atoms where

import Control.DeepSeq
import GHC.Generics (Generic, Generic1)

import AlgPrelude


type L1 a = Sum2 () (Pair2 Int a)
type L2 a = Sum2 () (Pair2 (Pair2 Int Int) a)
type P a = Sum2 (Sum2 () (Pair2 Int Int)) (Pair2 a a)

data RecL1
  = L1Inj0_2 ()
  | L1Inj1_2 Int RecL1
  deriving Generic

fromL1 (L1Inj0_2 _) = []
fromL1 (L1Inj1_2 h t) = h : fromL1 t

toL1 [] = L1Inj0_2 ()
toL1 (h:t) = L1Inj1_2 h $! toL1 t

instance () => NFData RecL1

inL1 (Inj0_2 v0) = L1Inj0_2 v0
inL1 (Inj1_2 (Pair2 v0 v1)) = L1Inj1_2 v0 v1

outL1 (L1Inj0_2 v0) = Inj0_2 v0
outL1 (L1Inj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)

data RecL2
  = L2Inj0_2 ()
  | L2Inj1_2 (Pair2 Int Int) RecL2
  deriving Generic

fromL2 (L2Inj0_2 _) = []
fromL2 (L2Inj1_2 h t) = h : fromL2 t

toL2 [] = L2Inj0_2 ()
toL2 (h:t) = L2Inj1_2 h $! toL2 t

instance () => NFData RecL2

inL2 (Inj0_2 v0) = L2Inj0_2 v0
inL2 (Inj1_2 (Pair2 v0 v1)) = L2Inj1_2 v0 v1

outL2 (L2Inj0_2 v0) = Inj0_2 v0
outL2 (L2Inj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)

data RecP
  = PInj0_2 (Sum2 () (Pair2 Int Int))
  | PInj1_2 RecP RecP

inP (Inj0_2 v0) = PInj0_2 v0
inP (Inj1_2 (Pair2 v0 v1)) = PInj1_2 v0 v1

outP (PInj0_2 v0) = Inj0_2 v0
outP (PInj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)

imult :: Pair2 Int Int -> Int
imult (Pair2 i j) = i * j

isum :: Pair2 Int Int -> Int
isum (Pair2 i j) = i + j

split :: RecL2 -> Sum2 (Sum2 () (Pair2 Int Int)) (Pair2 RecL2 RecL2)
split (L2Inj0_2 v) = Inj0_2 $! Inj0_2 v
split (L2Inj1_2 h (L2Inj0_2 _)) = Inj0_2 $! Inj1_2 h
split (L2Inj1_2 h1 (L2Inj1_2 h2 t))
  = Inj1_2 $! go (L2Inj1_2 h1 (L2Inj0_2 ())) (L2Inj1_2 h2 (L2Inj0_2 ())) t
  where
    go l r (L2Inj0_2 _) = Pair2 l r
    go l r (L2Inj1_2 h t) = go r (L2Inj1_2 h l) t

