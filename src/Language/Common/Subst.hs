{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Common.Subst
  ( Subst(..)
  , Env
  , emptySubst
  ) where

import Data.Map.Strict

type Env a = Map Int a

emptySubst :: Env a
emptySubst = empty

class Subst a t | t -> a where
  subst :: Env a -> t -> t
