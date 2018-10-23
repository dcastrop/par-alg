module Language.Internal.Id
  ( Id
  , mkId
  ) where

import Data.Text.Prettyprint.Doc

data Id = Id { getId :: Int, getLbl :: String }

mkId :: Int -> String -> Id
mkId = Id

instance Eq Id where
  i == j = getId i == getId j

instance Ord Id where
  i `compare` j = getId i `compare` getId j

instance Pretty Id where
  pretty = pretty . getLbl
