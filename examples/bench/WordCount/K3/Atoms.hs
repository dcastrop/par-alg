{-# LANGUAGE DeriveGeneric #-}
module Atoms where

import           Control.DeepSeq
import           GHC.Generics       (Generic, Generic1)

import           Data.Vector        ( Vector )
import qualified Data.Vector     as Vector
import           Data.Map.Strict    ( Map )
import qualified Data.Map.Strict as Map
import           Data.List          ( foldl' )
import           Data.Text          ( Text   )
import qualified Data.Text       as Text

import           AlgPrelude

threshold = 100

type L1 a = Sum2 () (Pair2 Text a)
type T a = Sum2 (RecL1) (Pair2 a a)
type D a = Sum2 () (Pair2 (Pair2 Text Int) a)
type Dict = RecD

type RecL1 = Vector Text

-- inL1 (Inj0_2 _) = []
-- inL1 (Inj1_2 (Pair2 v0 v1)) = v0 : v1
--
-- outL1 [] = Inj0_2 ()
-- outL1 (v0 : v1) = Inj1_2 (Pair2 v0 v1)

data RecT
  = TInj0_2 (RecL1)
  | TInj1_2 RecT RecT
  deriving Generic
instance NFData RecT

inT (Inj0_2 v0) = TInj0_2 v0
inT (Inj1_2 (Pair2 v0 v1)) = TInj1_2 v0 v1

outT (TInj0_2 v0) = Inj0_2 v0
outT (TInj1_2 v0 v1) = Inj1_2 (Pair2 v0 v1)

type RecD = Map Text Int

inD (Inj0_2 ()) = Map.empty
inD (Inj1_2 (Pair2 v0 v1)) = uncurry Map.insert v0 v1

outD d
  | Map.null d = Inj0_2 ()
  | otherwise  = Inj1_2 (Pair2 v0 v1)
  where
    (v0, v1) = Map.deleteFindMin d

spltw :: Text -> RecL1
spltw t = Vector.fromList $! Text.words t

union :: Pair2 Dict Dict-> Dict
union (Pair2 l r) = Map.unionWith (+) l r

count :: RecL1 -> Dict
count = Vector.foldl' (flip $ Map.alter go) Map.empty
  where
    go Nothing = Just 1
    go (Just i) = Just $! i+1

split :: RecL1 -> Sum2 (RecL1) (Pair2 RecL1 RecL1)
split l
  | n  < 1000 = Inj0_2 l
  | otherwise = Inj1_2 $! Pair2 l1 l2
  where
    n = Vector.length l
    (l1, l2) = Vector.splitAt (n `div` 2) l

