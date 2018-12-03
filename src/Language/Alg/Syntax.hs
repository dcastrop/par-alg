{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Alg.Syntax
  ( Poly(..)
  , pSum
  , pPrd
  , Func
  , Alg(..)
  , comp
  , fsum
  , fprod
  , Ftv(..)
  , Mv(..)
  , Type(..)
  , Scheme(..)
  , substVar
  , Subst(..)
  , RwStrat(..)
  , rwSeq
  , substPoly
  , tSum
  , tPrd
  , tFun
  , Def(..)
  , TyDef(..)
  , TyEnv
  , Prog(..)
  ) where

import Control.Arrow ( (***) )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map.Strict ( Map )

import Language.Common.Id
import Language.Common.Subst

-- | Free type variables
class Ftv a where
  ftv :: a -> Set Id

class Mv a where
  metaVars :: a -> Set Int

data Poly a
  = PK !a
  | PV !Id
  | PI
  | PPrd ![Poly a]
  | PSum ![Poly a]
  | PMeta !Int -- ^ metavariables
  deriving (Eq, Ord, Show)

substPoly :: Env (Poly a) -> Poly a -> Poly a
substPoly e = go
  where
    go x@(PMeta i)
      | Just p <- Map.lookup i e = go p
      | otherwise               = x
    go x@PK{}    = x
    go x@PV{}    = x
    go x@PI{}    = x
    go (PPrd ps) = PPrd $! map go ps
    go (PSum ps) = PSum $! map go ps

instance Subst a t => Subst a (Poly t) where
  subst e = go
    where
      go (PK t)    = PK $! subst e t
      go x@PV{}    = x
      go x@PI{}    = x
      go x@PMeta{} = x
      go (PPrd ps) = PPrd $! map go ps
      go (PSum ps) = PSum $! map go ps

substVarP :: Map Id (Type a) -> Poly (Type a) -> Poly (Type a)
substVarP e = go
  where
    go (PK t)    = PK $! substVar e t
    go x@PV{}    = x
    go x@PI{}    = x
    go x@PMeta{} = x
    go (PPrd ps) = PPrd $! map go ps
    go (PSum ps) = PSum $! map go ps

pSum, pPrd :: Show a => Poly a -> Poly a -> Poly a
pSum (PSum xs) y = PSum $! xs ++ [y]
pSum l r = PSum [l,r]
pPrd (PPrd xs) y = PPrd $! xs ++ [y]
pPrd l r = PPrd [l,r]

instance Ftv a => Ftv (Poly a) where
  ftv (PK t)    = ftv t
  ftv PV{}      = Set.empty
  ftv PI{}      = Set.empty
  ftv PMeta{}   = Set.empty
  ftv (PPrd ps) = Set.unions $! fmap ftv ps
  ftv (PSum ps) = Set.unions $! fmap ftv ps

instance Mv (Poly a) where
  metaVars PK{}      = Set.empty
  metaVars PV{}      = Set.empty
  metaVars PI{}      = Set.empty
  metaVars (PMeta i) = Set.singleton i
  metaVars (PPrd ps) = Set.unions $! fmap metaVars ps
  metaVars (PSum ps) = Set.unions $! fmap metaVars ps

metaVarsP :: Mv a => Poly a -> Set Int
metaVarsP (PK t)    = metaVars t
metaVarsP PV{}      = Set.empty
metaVarsP PI{}      = Set.empty
metaVarsP PMeta{}   = Set.empty
metaVarsP (PPrd ps) = Set.unions $! fmap metaVarsP ps
metaVarsP (PSum ps) = Set.unions $! fmap metaVarsP ps

type Func a = Poly (Type a)

data Type a
  = TPrim !a
  | TVar !Id
  | TUnit
  | TFun ![Type a]
  | TSum ![Type a] !(Maybe Int)
  | TPrd ![Type a] !(Maybe Int)
  | TApp !(Func a) !(Type a)
  | TRec !(Func a)
  | TMeta !Int
  deriving (Eq, Ord, Show)

substVar :: Map Id (Type a) -> Type a -> Type a
substVar e = go
  where
    go x@TPrim{}   = x
    go x@(TVar i)
      | Just t <- Map.lookup i e = t
      | otherwise               = x
    go x@TUnit{}   = x
    go (TFun ts)   = TFun $! map go ts
    -- XXX: careful, substitutions of sums and prods may extend the number
    -- of elements. See unification rules
    go (TSum ts t) = TSum (map go ts) t
    go (TPrd ts t) = TPrd (map go ts) t
    go (TApp f t)  = TApp (substVarP e f) $! go t
    go (TRec f)    = TRec $! substVarP e f
    go x@TMeta{}   = x

instance Subst (Type a) (Type a) where
  subst e = go
    where
      go x@TPrim{}   = x
      go x@TVar{}    = x
      go x@TUnit{}   = x
      go (TFun ts)   = TFun $! map go ts
      -- XXX: careful, substitutions of sums and prods may extend the number
      -- of elements. See unification rules
      go (TSum ts t) = TSum (map go $! ts ++ ts') $! mt
        where
          (mt, ts') = aux t
          aux Nothing = (Nothing, [])
          aux j@(Just i)
            | Just (TSum ts1 t') <- Map.lookup i e
            = (id *** (ts1 ++)) $! aux t'
            | Just (TMeta t') <- Map.lookup i e
            = aux (Just t')
            | Just t1 <- Map.lookup i e
            = (Nothing, [t1])
            | otherwise
            = (j, [])
      go (TPrd ts t) = TPrd (map go $! ts ++ ts') $! mt
        where
          (mt, ts') = aux t
          aux Nothing = (Nothing, [])
          aux j@(Just i)
            | Just (TPrd ts1 t') <- Map.lookup i e
            = (id *** (ts1 ++)) $! aux t'
            | Just (TMeta t') <- Map.lookup i e
            = aux (Just t')
            | Just t1 <- Map.lookup i e
            = (Nothing, [t1])
            | otherwise
            = (j, [])
      go (TApp f t)  = TApp (subst e f) $! go t
      go (TRec f)    = TRec $! subst e f
      go x@(TMeta i)
        | Just t <- Map.lookup i e = go t
        | otherwise               = x

tSum, tPrd, tFun :: Type a -> Type a -> Type a
tSum (TSum xs t) y = TSum (xs ++ [y]) t
tSum l r = TSum [l, r] Nothing
tPrd (TPrd xs t) y = TPrd (xs ++ [y]) t
tPrd l r = TPrd [l, r] Nothing
tFun x (TFun ys) = TFun $! x : ys
tFun l r = TFun [l,r]

instance Ftv (Type a) where
  ftv TPrim{}      = Set.empty
  ftv TUnit{}      = Set.empty
  ftv (TVar v)     = Set.singleton v
  ftv (TFun ts)    = Set.unions $! fmap ftv ts
  ftv (TSum ts _)  = Set.unions $! fmap ftv $! ts
  ftv (TPrd ts _)  = Set.unions $! fmap ftv $! ts
  ftv (TApp fn ts) = ftv fn `Set.union` ftv ts
  ftv (TRec fn)    = ftv fn
  ftv TMeta{}      = Set.empty

instance Mv (Type a) where
  metaVars TPrim{}      = Set.empty
  metaVars TUnit{}      = Set.empty
  metaVars TVar{}       = Set.empty
  metaVars (TFun ts)    = Set.unions $! fmap metaVars ts
  metaVars (TSum ts i)  = Set.union (maybe Set.empty Set.singleton i) $!
                          Set.unions $! fmap metaVars $! ts
  metaVars (TPrd ts i)  = Set.union (maybe Set.empty Set.singleton i) $!
                          Set.unions $! fmap metaVars $! ts
  metaVars (TApp fn ts) = metaVarsP fn `Set.union` metaVars ts
  metaVars (TRec fn)    = metaVarsP fn
  metaVars (TMeta i)    = Set.singleton i


data Scheme a
  = ForAll { scVars :: !(Set Id)
           , scType :: !(Type a)
           }
  deriving (Eq, Show)

data Alg t v
  = Var !Id
  | Val !v
  | Const !(Alg t v)
  | Unit
  | Comp ![Alg t v]
  | Id
  -- Products
  | Proj !Int !Int
  | Split ![Alg t v]
  -- Sums
  | Inj !Int !Int
  | Case ![Alg t v]
  -- Distributivity
  | Dist !Int !Int !Int
  | Fmap !(Func t) !(Alg t v)
  | In  !(Func t)
  | Out !(Func t)
  | Rec !Id !(Func t) !(Alg t v) !(Alg t v)
  deriving (Eq, Ord, Show)

fsum :: [Alg t v] -> Alg t v
fsum ts = Case $! zipWith (comp . (`Inj` length ts)) [0..] ts
fprod :: [Alg t v] -> Alg t v
fprod ts = Split $! zipWith (flip comp . (`Proj` length ts)) [0..] ts

instance Subst (Func t) (Alg t v) where
  subst s ( Const e       ) = Const (subst s e)
  subst s ( Comp es       ) = Comp $! map (subst s) es
  subst s ( Split es      ) = Split $! map (subst s) es
  subst s ( Case es       ) = Case $! map (subst s) es
  subst s ( Fmap f e      ) = Fmap (substPoly s f) (subst s e)
  subst s ( In  f         ) = In (substPoly s f)
  subst s ( Out f         ) = Out (substPoly s f)
  subst s ( Rec n f e1 e2 ) = Rec n (substPoly s f) (subst s e1) (subst s e2)
  subst _ t                 = t

comp :: Alg t v -> Alg t v -> Alg t v
comp Id e = e
comp e Id = e
comp (Comp xs) (Comp ys) = Comp $! xs ++ ys
comp (Comp xs) y         = Comp $! xs ++ [y]
comp x         (Comp ys) = Comp $! x : ys
comp x         y         = Comp [x, y]

data RwStrat t v
  = Unroll !Int
  | Annotate (Set (Alg t v))

  | RwRefl
  | RwSeq !(RwStrat t v) !(RwStrat t v)
  deriving Show

rwSeq :: RwStrat t v -> RwStrat t v -> RwStrat t v
rwSeq RwRefl r = r
rwSeq r RwRefl = r
rwSeq r1 r2 = RwSeq r1 r2


data Def t v
  = FDef  !Id !(Func t)
  | TDef  !Id !(Type t)
  | EDef  !Id !(Scheme t) !(Alg t v)
  | EPar  !Id !Id !(RwStrat t v)
  | Atom  !Id !(Type t)
  deriving Show

newtype Prog t v
  = Prog { getDefns :: [Def t v]
         }
  deriving Show

data TyDef t
  = AnnF (Func t) -- Functors
  | AnnT (Type t) -- Types
  | AnnA (Type t) -- Atoms

type TyEnv t = Map Id (TyDef t)
