module Language.Alg.Syntax
  ( Poly(..)
  , Alg(..)
  , Type(..)
  ) where

import qualified Prelude
import Prelude hiding ( (.), id )

import

data Poly a
  = PK a
  | PI
  | PPrd [Poly a]
  | PSum [Poly a]
  | PVar Id

pcomp :: Poly a -> Poly a -> Poly a
pcomp f@PK{}    g = f
pcomp PI        g = g
pcomp (PPrd fs) g = PPrd $ fmap (`pcomp` g) fs
pcomp (PSum fs) g = PSum $ fmap (`pcomp` g) fs

type Func a = Poly (Type a)

data Type a
  = TPrim a
  | TUnit
  | TFun (Type a) (Type a)
  | TSum [Type a]
  | TPrd [Type a]
  | TRec (Func a)

data Alg t a
  = Atom a
  | Unit
  | Comp (Alg t a) (Alg t a)
  | Id
  | Proj Int
  | Split [Alg t a]
  | Inj Int
  | Case [Alg t a]
  | In (Func t)
  | Out (Func t)
  | Rec (Func t) (Alg t a) (Alg t a)
