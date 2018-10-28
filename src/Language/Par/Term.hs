module Language.Par.Term
  ( ATerm (..)
  ) where

import Language.Alg.Syntax

import Language.Par.Role

data ATerm t v
  = TmAnn (Alg t v) RoleId
  | TmId
  | TmComp [ATerm t v]
  | TmPrj Int
  | TmSplit [ATerm t v]
  | TmInj Int
  | TmCase [ATerm t v]
  | TmApp (Func t) Role (Alg t v)
