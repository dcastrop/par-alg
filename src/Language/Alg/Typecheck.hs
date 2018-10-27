{-# LANGUAGE ConstraintKinds #-}
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

import Control.Arrow ( (***) )
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

type SEnv t = (Env (Func t), Env (Type t))

class TypeOf t v a | a -> t where
  checkType :: Env a -> v -> a -> TcM t (Env a)

class KindChecker t where
  checkKind :: Set Id -> t -> TcM a ()

type Prim v t = (KindChecker t, Eq t, Pretty t, Pretty v, Ftv t, TypeOf t v (Type t))

checkProg :: Prim v t => Prog t v -> TcM t ()
checkProg = mapM_ checkDef . getDefns

checkDef :: Prim v t => Def t v -> TcM t ()
checkDef (FDef v f)   = checkKind Set.empty f *> newPoly v f
checkDef (TDef v f)   = checkKind Set.empty f *> newType v f
checkDef (Atom v t)   = checkKind Set.empty t *> newFun v (ForAll Set.empty t)
checkDef (EDef i s f) = do
  checkKind (scVars s) (scType s)
  _ <- typeOf (emptySubst, emptySubst) f (scType s)
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

-- FIXME: Refactor, use StateT for typeOf with environments, or (since metavars are
-- introduced fresh), just add Env (Type t) to state. However, there is no need to
-- keep environment of metavars after typechecking definition!
typeOf :: Prim v t => SEnv t -> Alg t v -> Type t -> TcM t (SEnv t)
typeOf s (Var x      ) t
  = lookupVar x >>= skolemise >>= (`unif` t)
  where unif = unify s
typeOf s (Val v      ) t
  = checkType (snd s) v t >>= \s' -> return (fst s, s')
typeOf s (Const e    ) t
  = do t1 <- TMeta <$> fresh
       t2 <- TMeta <$> fresh
       s' <- unify s t (t1 `tFun` t2)
       typeOf s' e t2
typeOf s (Unit       ) t
  = unify s t TUnit
typeOf s (Comp es    ) t
  = do dom <- TMeta <$> fresh
       cod <- TMeta <$> fresh
       s' <- unify s t (dom `tFun` cod)
       go s' es dom cod
  where
    go _  []     _d _c = error $ "Panic! Empty composition"
    go s0 [e]     d  c = typeOf s0 e (d `tFun` c)
    go s0 (x:xs)  d  c = do
      ti <- TMeta <$> fresh
      s1 <- go s0 xs d ti
      typeOf s1 x (ti `tFun` c)
typeOf s (Id         ) t = do
  t1 <- TMeta <$> fresh
  unify s t (t1 `tFun` t1)
typeOf s (Proj i     ) t = do
  ts <- mapM (const (TMeta <$> fresh)) [0..i]
  m  <- Just <$> fresh
  unify s t (tFun (TPrd ts m) $ last ts)
typeOf s e@(Split es   ) t
  | length es < 2 = fail $ "Ill-formed split: " ++ render e
  | otherwise = do
      ti  <- TMeta <$> fresh
      ts  <- mapM (const (TMeta <$> fresh)) es
      s'  <- unify s t (ti `tFun` TPrd ts Nothing)
      foldM ( uncurry . typeOf) s' $ zip es $ map (tFun ti) ts
typeOf s (Inj  i     ) t = do
  ts <- mapM (const (TMeta <$> fresh)) [0..i]
  m  <- Just <$> fresh
  unify s t (tFun (last ts) (TSum ts m))
typeOf s e@(Case es   ) t
  | length es < 2 = fail $ "Ill-formed case: " ++ render e
  | otherwise = do
      ts  <- mapM (const (TMeta <$> fresh)) es
      to  <- TMeta <$> fresh
      s'  <- unify s t (TSum ts Nothing `tFun` to)
      foldM (uncurry . typeOf) s' $ zip es $ map (`tFun` to) ts
typeOf s (Fmap f e   ) t = do
  a <- TMeta <$> fresh
  b <- TMeta <$> fresh
  s' <- unify s t (TApp f a `tFun` TApp f b)
  typeOf s' e (a `tFun` b)
typeOf s (In f       ) t =
  unify s t $ TApp f (TRec f) `tFun` TRec f
typeOf s (Out f      ) t =
  unify s t $ TRec f `tFun` TApp f (TRec f)
typeOf s (Rec f e1 e2) t = do
  a <- TMeta <$> fresh
  b <- TMeta <$> fresh
  s'  <- unify s t (a `tFun` b)
  s'' <- typeOf s' e2 (a `tFun` TApp f a)
  typeOf s'' e1 (TApp f b `tFun` b)

unifyPoly :: (Eq t, Pretty t, IsCompound t) => Poly t -> Poly t -> TcM a (Env (Poly t))
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
--
--unifyP :: (Eq t, Pretty t) => Func t -> Func t -> TcM t (Env (Type t))
--unifyP (PK i) (PK j)
--  = unify i j
--unifyP (PPrd ps1) (PPrd ps2)
--  = foldM (\s (l, r) -> Map.union s <$> unifyP l (subst s r)) emptySubst $
--    zip ps1 ps2
--unifyP (PSum ps1) (PSum ps2)
--  = foldM (\s (l, r) -> Map.union s <$> unifyP l (subst s r)) emptySubst $
--    zip ps1 ps2
--unifyP t1    t2
--  | t1 == t2   = return emptySubst
--  | otherwise = fail $ "Cannot unify '" ++ render t1 ++ "' with '" ++ render t2 ++ "'"
--
--
zipD :: [a] -> [a] -> ([(a,a)], MEither [a] [a]) -- Return remaining elements
zipD [] [] = ([], None)
zipD [] r  = ([], JRight r)
zipD l  [] = ([], JLeft l)
zipD (l:ls) (r:rs) = ((l,r):lrs , m)
  where
    (lrs, m) = zipD ls rs

data MEither a b
  = None
  | JLeft  a
  | JRight b

zipF :: [Type a] -> [Type a] -> [(Type a, Type a)] -- Return remaining elements
zipF xs ys =
  case zipD xs ys of
    (l, None)     -> l
    (l, JRight r) -> init l ++ [(id *** (TFun . (:r))) $ last l]
    (l, JLeft  r) -> init l ++ [((TFun . (:r)) *** id) $ last l]

-- app :: Func t -> Type t -> TcM t (Type t)
-- app (PK    t       )
-- app (PV    v       )
-- app  PI
-- app (PPrd  ps      )
-- app (PSum  ps      )
-- app (PMeta i       ) _ = fail
--   "Cannot apply "

unify :: (Eq t, Pretty t) => SEnv t -> Type t -> Type t -> TcM t (SEnv t)
unify s t x@(TMeta i)
  | Just t' <- Map.lookup i (snd s)  = unify s t t'
  | i `Set.member` metaVars t = fail $ "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render t ++ "'"
  | otherwise                 = pure $ (id *** Map.insert i t) s
unify s x@TMeta{} t = unify s t x
unify s0 (TFun ts1) (TFun ts2) = foldM (uncurry . unify) s0 $ zipF ts1 ts2
unify s0 t1@(TSum ts1 mii) t2@(TSum ts2 mjj)
  = do s1 <- foldM (uncurry . unify) s0 ts
       unifyTail msg TSum s1 m mii mjj
  where
    (ts, m) = zipD ts1 ts2
    msg = "Cannot unify '" ++ render t1 ++ "' with '" ++ render t2 ++ "'"
unify s0 t1@(TPrd ts1 mii) t2@(TPrd ts2 mjj)
  = do s1 <- foldM (uncurry . unify) s0 ts
       unifyTail msg TPrd s1 m mii mjj
  where
    (ts, m) = zipD ts1 ts2
    msg = "Cannot unify '" ++ render t1 ++ "' with '" ++ render t2 ++ "'"
--unify s0 (TApp f1 t1) (TApp f2 t2) = do
--  sp <- unifyPoly (fst s0) f1 f2
--  s1 <- unifyP f1 (substPoly sp f2)
--  s2 <- unify t1 (subst s1 t2)
--  return $ Map.union s1 s2
--unify (TRec f1) (TRec f2) = do
--  sp <- unifyPoly f1 f2
--  unifyP f1 (substPoly sp f2)
unify s t1 t2
  | t1 == t2   = pure s
  | otherwise = fail $ "Cannot unify '" ++ render t1 ++ "' with '" ++ render t2 ++ "'"


-- Unify products/sums with different num of elements
unifyTail :: (Eq t, Pretty t)
          => String
          -> ([Type t] -> Maybe Int -> Type t)
          -> SEnv t
          -> MEither [Type t] [Type t]
          -> Maybe Int
          -> Maybe Int
          -> TcM t (SEnv t)
unifyTail _      spr s None Nothing  Nothing  = return s
unifyTail _      spr s None (Just i) mj       = unify s (spr [] mj) (TMeta i)
unifyTail _      spr s None mi (Just j)       = unify s (spr [] mi) (TMeta j)
unifyTail _      spr s (JLeft l) mi (Just j)  = unify s (spr l  mi) (TMeta j)
unifyTail msgerr _   _ (JLeft _) _  Nothing   = fail msgerr
unifyTail _      spr s (JRight l) (Just i) mj = unify s (spr l  mj) (TMeta i)
unifyTail msgerr _   _ (JRight _) Nothing  _  = fail msgerr
