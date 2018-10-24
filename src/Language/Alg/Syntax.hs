module Language.Alg.Syntax
  ( Poly(..)
  , pSum
  , pPrd
  , Func
  , Alg(..)
  , Type(..)
  , tSum
  , tPrd
  , tFun
  ) where

import Language.Internal.Id

data Poly a
  = PK a
  | PV Id
  | PI
  | PPrd [Poly a]
  | PSum [Poly a]
  deriving (Eq, Show)

pSum, pPrd :: Show a => Poly a -> Poly a -> Poly a
pSum (PSum xs) y = PSum $ xs ++ [y]
pSum l r = PSum [l,r]
pPrd (PPrd xs) y = PPrd $ xs ++ [y]
pPrd l r = PPrd [l,r]

type Func a = Poly (Type a)

data Type a
  = TPrim a
  | TUnit
  | TFun [Type a]
  | TSum [Type a]
  | TPrd [Type a]
  | TApp (Func a) (Type a)
  | TRec (Func a)
  deriving (Eq, Show)

tSum, tPrd, tFun :: Type a -> Type a -> Type a
tSum (TSum xs) y = TSum $ xs ++ [y]
tSum l r = TSum [l,r]
tPrd (TPrd xs) y = TPrd $ xs ++ [y]
tPrd l r = TPrd [l,r]
tFun x (TFun ys) = TFun $ x : ys
tFun l r = TFun [l,r]

data Alg t v
  = Var  Id
  | Val v
  | Const (Alg t v)
  | Unit
  | Comp [Alg t v]
  | Id
  | Proj Int
  | Split [Alg t v]
  | Inj Int
  | Case [Alg t v]
  | In  (Maybe (Func t))
  | Out (Maybe (Func t))
  | Rec (Func t) (Alg t v) (Alg t v)
  deriving (Eq, Show)
