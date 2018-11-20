module Language.Common.Id
  ( Id
  , getId
  , getLbl
  , mkId
  , Fresh(..)
  , IdGen(..)
  , freshId
  , knownId
  , rename
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
  -- pretty i = hcat [pretty $ getLbl i, pretty $ getId i]
  pretty i = pretty $ getLbl i

class Monad m => Fresh m where
  fresh :: m Int

class Fresh m => IdGen m where
  newId :: Id     -> m ()
  lookupId :: String -> m (Maybe Id)

freshId :: IdGen m => String -> m Id
freshId s = Id <$> fresh <*> pure s >>= \i -> newId i *> pure i

knownId :: IdGen m => String -> m Id
knownId s = lookupId s >>= maybe (fail $ "Unknown id '" ++ s ++ "'") pure

rename :: IdGen m => Id -> m Id
rename i = do
  fn <- fresh
  let nid = Id fn (getLbl i ++ show fn)
  newId nid
  pure nid
