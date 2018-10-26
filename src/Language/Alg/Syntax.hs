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
  , Mv(..)
  , Type(..)
  , Scheme(..)
  , Subst(..)
  , substPoly
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

class Mv a where
  metaVars :: a -> Set Int

data Poly a
  = PK a
  | PV Id
  | PI
  | PPrd [Poly a]
  | PSum [Poly a]
  | PMeta Int -- ^ metavariables
  deriving (Eq, Show)

substPoly :: Env (Poly a) -> Poly a -> Poly a
substPoly e = go
  where
    go x@(PMeta i)
      | Just p <- Map.lookup i e = go p
      | otherwise               = x
    go x@PK{}    = x
    go x@PV{}    = x
    go x@PI{}    = x
    go (PPrd ps) = PPrd $ map go ps
    go (PSum ps) = PSum $ map go ps

instance Subst a t => Subst a (Poly t) where
  subst e = go
    where
      go (PK t)    = PK $ subst e t
      go x@PV{}    = x
      go x@PI{}    = x
      go x@PMeta{} = x
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
  ftv PMeta{}   = Set.empty
  ftv (PPrd ps) = Set.unions $ fmap ftv ps
  ftv (PSum ps) = Set.unions $ fmap ftv ps

instance Mv (Poly a) where
  metaVars PK{}      = Set.empty
  metaVars PV{}      = Set.empty
  metaVars PI{}      = Set.empty
  metaVars (PMeta i) = Set.singleton i
  metaVars (PPrd ps) = Set.unions $ fmap metaVars ps
  metaVars (PSum ps) = Set.unions $ fmap metaVars ps

metaVarsP :: Mv a => Poly a -> Set Int
metaVarsP (PK t)    = metaVars t
metaVarsP PV{}      = Set.empty
metaVarsP PI{}      = Set.empty
metaVarsP PMeta{}   = Set.empty
metaVarsP (PPrd ps) = Set.unions $ fmap metaVarsP ps
metaVarsP (PSum ps) = Set.unions $ fmap metaVarsP ps

type Func a = Poly (Type a)

data Type a
  = TPrim a
  | TVar Id
  | TUnit
  | TFun [Type a]
  | TSum [Type a] (Maybe Int)
  | TPrd [Type a] (Maybe Int)
  | TApp (Func a) (Type a)
  | TRec (Func a)
  | TMeta Int
  deriving (Eq, Show)

instance Subst (Type a) (Type a) where
  subst e = go
    where
      go x@TPrim{}   = x
      go x@TVar{}    = x
      go x@TUnit{}   = x
      go (TFun ts)   = TFun $ map go ts
      go (TSum ts t) = TSum (map go ts) t
      go (TPrd ts t) = TPrd (map go ts) t
      go (TApp f t)  = TApp (subst e f) $ go t
      go (TRec f)    = TRec $ subst e f
      go x@(TMeta i)
        | Just t <- Map.lookup i e = go t
        | otherwise               = x

tSum, tPrd, tFun :: Type a -> Type a -> Type a
tSum (TSum xs t) y = TSum (xs ++ [y]) t
tSum l r = TSum [l, r] Nothing
tPrd (TPrd xs t) y = TPrd (xs ++ [y]) t
tPrd l r = TPrd [l, r] Nothing
tFun x (TFun ys) = TFun $ x : ys
tFun l r = TFun [l,r]

instance Ftv (Type a) where
  ftv TPrim{}      = Set.empty
  ftv TUnit{}      = Set.empty
  ftv (TVar v)     = Set.singleton v
  ftv (TFun ts)    = Set.unions $ fmap ftv ts
  ftv (TSum ts _)  = Set.unions $ fmap ftv $ ts
  ftv (TPrd ts _)  = Set.unions $ fmap ftv $ ts
  ftv (TApp fn ts) = ftv fn `Set.union` ftv ts
  ftv (TRec fn)    = ftv fn
  ftv TMeta{}      = Set.empty

instance Mv (Type a) where
  metaVars TPrim{}      = Set.empty
  metaVars TUnit{}      = Set.empty
  metaVars TVar{}       = Set.empty
  metaVars (TFun ts)    = Set.unions $ fmap metaVars ts
  metaVars (TSum ts i)  = Set.union (maybe Set.empty Set.singleton i) $
                          Set.unions $ fmap metaVars $ ts
  metaVars (TPrd ts i)  = Set.union (maybe Set.empty Set.singleton i) $
                          Set.unions $ fmap metaVars $ ts
  metaVars (TApp fn ts) = metaVarsP fn `Set.union` metaVars ts
  metaVars (TRec fn)    = metaVarsP fn
  metaVars (TMeta i)    = Set.singleton i


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
  | In  (Func t)
  | Out (Func t)
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
