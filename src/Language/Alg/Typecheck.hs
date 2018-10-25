{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Alg.Typecheck
  ( KindChecker (..)
  , TypeChecker (..)
  , checkProg
  , checkDef
  ) where

import Data.Set ( Set )
import qualified Data.Set as Set

import Language.Common.Id
import Language.Alg.Syntax
import Language.Alg.Internal.TcM

class TypeChecker v t where
  hasType :: v -> t -> TcM a ()
  infer   :: v -> TcM a t

class KindChecker t where
  checkKind :: Set Id -> t -> TcM a ()

checkProg :: (KindChecker t, TypeChecker v t) => Prog t v -> TcM t ()
checkProg = mapM_ checkDef . getDefns

checkDef :: (KindChecker t, TypeChecker v t) => Def t v -> TcM t ()
checkDef (FDef v f)   = checkKind Set.empty f *> newPoly v f
checkDef (TDef v f)   = checkKind Set.empty f *> newType v f
checkDef (Atom v t)   = checkKind Set.empty t *> newFun v (ForAll Set.empty t)
checkDef (EDef i s f) = do
  checkKind (scVars s) (scType s)
  f `hasType` scType s
  newFun i s

instance KindChecker t => KindChecker (Poly t) where
  checkKind vs (PK t)   = (checkKind vs) t
  checkKind  _ PI       = return ()
  checkKind  _ (PV i)   = polyDefined i
  checkKind vs (PPrd p) = mapM_ (checkKind vs) p
  checkKind vs (PSum p) = mapM_ (checkKind vs) p

instance KindChecker t => KindChecker (Type t) where
  checkKind vs (TPrim t)  = (checkKind vs) t
  checkKind vs (TVar v)
    | v `Set.member` vs = return ()
    | otherwise         = typeDefined v
  checkKind  _ TUnit      = return ()
  checkKind vs (TFun t)   = mapM_ (checkKind vs) t
  checkKind vs (TSum t)   = mapM_ (checkKind vs) t
  checkKind vs (TPrd t)   = mapM_ (checkKind vs) t
  checkKind vs (TApp f t) = (checkKind vs) f >> (checkKind vs) t
  checkKind vs (TRec f)   = (checkKind vs) f
  checkKind  _ (TMeta _)  = fail "Unexpected metavariable when checking type"


instance TypeChecker v t => TypeChecker (Alg t v) (Type t) where
  hasType = undefined

  infer = undefined
