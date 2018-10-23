module Language.Alg.Syntax
  ( Poly(..)
  , Func
  , Alg(..)
  , Type(..)
  ) where

import Language.Internal.Id

data Poly a
  = PK a
  | PV Id
  | PI
  | PPrd [Poly a]
  | PSum [Poly a]

type Func a = Poly (Type a)

data Type a
  = TPrim a
  | TUnit
  | TFun [Type a]
  | TSum [Type a]
  | TPrd [Type a]
  | TApp Id (Type a)
  | TRec (Func a)

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
