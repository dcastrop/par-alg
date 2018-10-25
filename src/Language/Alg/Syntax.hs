{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Alg.Syntax
  ( Poly(..)
  , pSum
  , pPrd
  , Func
  , Alg(..)
  , Ftv(..)
  , Type(..)
  , Scheme(..)
  , Subst(..)
  , tSum
  , tPrd
  , tFun
  , Def(..)
  , Prog(..)
  ) where

import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map

import Language.Common.Id
import Language.Common.Subst

-- | Free type variables
class Ftv a where
  ftv :: a -> Set Id

data Poly a
  = PK a
  | PV Id
  | PI
  | PPrd [Poly a]
  | PSum [Poly a]
  deriving (Eq, Show)

instance Subst a t => Subst a (Poly t) where
  subst e = go
    where
      go (PK t)    = PK $ subst e t
      go x@PV{}    = x
      go x@PI{}    = x
      go (PPrd ps) = PPrd $ map go ps
      go (PSum ps) = PSum $ map go ps

pSum, pPrd :: Show a => Poly a -> Poly a -> Poly a
pSum (PSum xs) y = PSum $ xs ++ [y]
pSum l r = PSum [l,r]
pPrd (PPrd xs) y = PPrd $ xs ++ [y]
pPrd l r = PPrd [l,r]

instance Ftv a => Ftv (Poly a) where
  ftv (PK t)    = ftv t
  ftv PV{}      = Set.empty
  ftv PI{}      = Set.empty
  ftv (PPrd ps) = Set.unions $ fmap ftv ps
  ftv (PSum ps) = Set.unions $ fmap ftv ps

type Func a = Poly (Type a)

data Type a
  = TPrim a
  | TVar Id
  | TUnit
  | TFun [Type a]
  | TSum [Type a]
  | TPrd [Type a]
  | TApp (Func a) (Type a)
  | TRec (Func a)
  | TMeta Int
  deriving (Eq, Show)

instance Subst (Type a) (Type a) where
  subst e = go
    where
      go x@TPrim{}  = x
      go x@TVar{}   = x
      go x@TUnit{}  = x
      go (TFun ts)  = TFun $ map go ts
      go (TSum ts)  = TSum $ map go ts
      go (TPrd ts)  = TPrd $ map go ts
      go (TApp f t) = TApp (subst e f) $ go t
      go (TRec f)   = TRec $ subst e f
      go x@(TMeta i)
        | Just t <- Map.lookup i e = t
        | otherwise               = x

tSum, tPrd, tFun :: Type a -> Type a -> Type a
tSum (TSum xs) y = TSum $ xs ++ [y]
tSum l r = TSum [l,r]
tPrd (TPrd xs) y = TPrd $ xs ++ [y]
tPrd l r = TPrd [l,r]
tFun x (TFun ys) = TFun $ x : ys
tFun l r = TFun [l,r]

instance Ftv (Type a) where
  ftv TPrim{}      = Set.empty
  ftv TUnit{}      = Set.empty
  ftv (TVar v)     = Set.singleton v
  ftv (TFun ts)    = Set.unions $ fmap ftv ts
  ftv (TSum ts)    = Set.unions $ fmap ftv ts
  ftv (TPrd ts)    = Set.unions $ fmap ftv ts
  ftv (TApp fn ts) = ftv fn `Set.union` ftv ts
  ftv (TRec fn)    = ftv fn
  ftv TMeta{}      = Set.empty

data Scheme a
  = ForAll { scVars :: Set Id
           , scType :: Type a
           }
  deriving (Eq, Show)

data Alg t v
  = Var  Id
  | Val v
  | Const (Alg t v)
  | Unit
  | Comp [Alg t v]
  | Id
  | Proj Integer
  | Split [Alg t v]
  | Inj Integer
  | Case [Alg t v]
  | Fmap (Func t) (Alg t v)
  | In  (Maybe (Func t))
  | Out (Maybe (Func t))
  | Rec (Func t) (Alg t v) (Alg t v)
  deriving (Eq, Show)

data Def t v
  = FDef  Id (Func t)
  | TDef  Id (Type t)
  | EDef  Id (Scheme t) (Alg t v)
  | Atom  Id (Type t)
  deriving Show

newtype Prog t v
  = Prog { getDefns :: [Def t v]
         }
  deriving Show
