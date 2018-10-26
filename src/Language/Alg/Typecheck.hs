{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Alg.Typecheck
  ( KindChecker (..)
  , TypeOf (..)
  , checkProg
  , checkDef
  ) where

import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad ( foldM )
import Data.Text.Prettyprint.Doc

import Language.Common.Id
import Language.Common.Subst
import Language.Alg.Syntax
import Language.Alg.Internal.TcM
import Language.Alg.Internal.Ppr

class TypeOf t v a | a -> t where
  typeOf :: v -> TcM t a

class KindChecker t where
  checkKind :: Set Id -> t -> TcM a ()

checkProg :: (KindChecker t, Ftv t, TypeOf t v t) => Prog t v -> TcM t ()
checkProg = mapM_ checkDef . getDefns

checkDef :: (KindChecker t, Ftv t, TypeOf t v t) => Def t v -> TcM t ()
checkDef (FDef v f)   = checkKind Set.empty f *> newPoly v f
checkDef (TDef v f)   = checkKind Set.empty f *> newType v f
checkDef (Atom v t)   = checkKind Set.empty t *> newFun v (ForAll Set.empty t)
checkDef (EDef i s f) = do
  checkKind (scVars s) (scType s)
  _ <- typeOf f >>= (`unify` scType s)
  newFun i s

instance KindChecker t => KindChecker (Poly t) where
  checkKind vs (PK t)   = (checkKind vs) t
  checkKind  _ PI       = return ()
  checkKind  _ (PV i)   = polyDefined i
  checkKind  _ PMeta{}  = fail "Undefined term in polynomial"
  checkKind vs (PPrd p) = mapM_ (checkKind vs) p
  checkKind vs (PSum p) = mapM_ (checkKind vs) p

instance KindChecker t => KindChecker (Type t) where
  checkKind vs (TPrim t)  = (checkKind vs) t
  checkKind vs (TVar v)
    | v `Set.member` vs = return ()
    | otherwise         = typeDefined v
  checkKind  _ TUnit      = return ()
  checkKind vs (TFun t)   = mapM_ (checkKind vs) t
  checkKind vs (TSum t _)   = mapM_ (checkKind vs) t
  checkKind vs (TPrd t _)   = mapM_ (checkKind vs) t
  checkKind vs (TApp f t) = (checkKind vs) f >> checkKind vs t
  checkKind vs (TRec f)   = (checkKind vs) f
  checkKind  _ (TMeta _)  = fail "Unexpected metavariable when checking type"

instance (Ftv t, TypeOf t v t) => TypeOf t (Alg t v) (Type t) where
  typeOf (Var x      )
    = lookupVar x >>= skolemise
  typeOf (Val v      )
    = TPrim <$> typeOf v
  typeOf (Const e    )
    = tFun <$> (TMeta <$> fresh) <*> typeOf e
  typeOf (Unit       )
    = return TUnit
  typeOf (Comp es    )
    = go es
    where
      go []     = error $ "Panic! Empty composition"
      go [e]    = typeOf e
      go (x:xs) = do
        t1 <- TMeta <$> fresh
        t2 <- TMeta <$> fresh
        t3 <- TMeta <$> fresh
        a1 <- go xs
        s1 <- unify a1 (t1 `tFun` t2)
        a2 <- typeOf x
        s2 <- unify a2 (subst s1 $ t2 `tFun` t3)
        return $ subst s2 (t1 `tFun` t3)
  typeOf (Id         ) = do
    t1 <- TMeta <$> fresh
    return $ t1 `tFun` t1
  typeOf (Proj i     ) = do
    ts <- mapM (const (TMeta <$> fresh)) [0..i]
    t  <- Just <$> fresh
    return (tFun (TPrd ts t) $ last ts)
  typeOf (Split es   ) = do
    ti <- TMeta <$> fresh
    ts <- mapM (const (TMeta <$> fresh)) es
    as <- mapM typeOf es
    s <- foldM (\s (l, r) -> unify l (subst s r)) emptySubst $
        zip as $ map (tFun ti) ts
    if length ts < 2
      then error $ "Panic! Product of less than 1 element"
      else return $ subst s (tFun ti (TPrd ts Nothing))
  typeOf (Inj i      ) = do
    ts <- mapM (const (TMeta <$> fresh)) [0..i]
    t  <- Just <$> fresh
    return (tFun (last ts) (TSum ts t))
  typeOf (Case es    ) = do
    ts <- mapM (const (TMeta <$> fresh)) es
    to <- TMeta <$> fresh
    as <- mapM typeOf es
    s <- foldM (\s (l, r) -> Map.union s <$> unify l (subst s r)) emptySubst $
        zip as $ map (`tFun` to) ts
    if length ts < 2
      then error $ "Panic! Sum of less than 1 element"
      else return $ subst s (tFun (TSum ts Nothing) to)
  typeOf (Fmap f e   ) = do
    a <- TMeta <$> fresh
    b <- TMeta <$> fresh
    t <- typeOf e
    s <- unify t (a `tFun` b)
    return $ subst s $ TApp f a  `tFun` TApp f b
  typeOf (In f       ) =
    return $ TApp f (TRec f) `tFun` TRec f
  typeOf (Out f      ) =
    return $ TRec f `tFun` TApp f (TRec f)
  typeOf (Rec f e1 e2) = do
    a <- TMeta <$> fresh
    b <- TMeta <$> fresh
    t1 <- typeOf e2
    t2 <- typeOf e1
    s1 <- unify t1 (a `tFun` TApp f a)
    s2 <- unify t2 (subst s1 $ TApp f b `tFun` b)
    return $ subst s2 $ a `tFun` b

unifyPoly :: (Eq t, Pretty t, IsCompound t) => Poly t -> Poly t -> TcM t (Env (Poly t))
unifyPoly p          x@(PMeta i)
  | i `Set.member` metaVars p = fail $ "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render p ++ "'"
  | otherwise = pure $ Map.insert i p emptySubst -- ^ metavariables
unifyPoly x@(PMeta i)  p
  | i `Set.member` metaVars p = fail $ "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render p ++ "'"
  | otherwise = pure $ Map.insert i p emptySubst
unifyPoly (PPrd ps1) (PPrd ps2)
  = foldM (\s (l, r) -> Map.union s <$> unifyPoly l (substPoly s r)) emptySubst $
    zip ps1 ps2
unifyPoly (PSum ps1) (PSum ps2)
  = foldM (\s (l, r) -> Map.union s <$> unifyPoly l (substPoly s r)) emptySubst $
    zip ps1 ps2
unifyPoly t1    t2
  | t1 == t2   = return emptySubst
  | otherwise = fail $ "Cannot unify '" ++ render t1 ++ "' with '" ++ render t2 ++ "'"

unify :: Type t -> Type t -> TcM t (Env (Type t))
unify = undefined
