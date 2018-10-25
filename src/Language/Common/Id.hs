module Language.Common.Id
  ( Id
  , getId
  , getLbl
  , mkId
  , IdGen(..)
  , freshId
  , knownId
  ) where

import Data.Text.Prettyprint.Doc

data Id = Id { getId :: Int, getLbl :: String }

mkId :: Int -> String -> Id
mkId = Id

instance Eq Id where
  i == j = getId i == getId j

instance Ord Id where
  i `compare` j = getId i `compare` getId j

instance Show Id where
  show = getLbl

instance Pretty Id where
  pretty = pretty . getLbl

class Monad m => IdGen m where
  fresh :: m Int
  newId :: Id     -> m ()
  lookupId :: String -> m (Maybe Id)

freshId :: IdGen m => String -> m Id
freshId s = mkId <$> fresh <*> pure s

knownId :: IdGen m => String -> m Id
knownId s = lookupId s >>= maybe (fail $ "Unknown id: " ++ s) pure
