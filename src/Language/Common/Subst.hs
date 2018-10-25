{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Common.Subst
  ( Subst(..)
  , Env
  ) where

import Data.Map.Strict

type Env a = Map Int a

class Subst a t | t -> a where
  subst :: Env a -> t -> t
