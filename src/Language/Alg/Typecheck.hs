{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Alg.Typecheck
  ( KindChecker (..)
  , TypeOf (..)
  , Prim
  , typecheck
  , checkProg
  , checkDef
  , tcTerm
  , execTcM
  , appPoly

  , protocol
  , inferGTy
  , tryChoice
  , requiresChoice
  , rAnn
  , rGet
  , roleTrack
  ) where

import Control.Monad ( zipWithM )
import qualified Data.Set as Set
import Data.List ( foldl' )
import Data.Map.Strict ( Map )
import Data.Traversable ( mapM )
import qualified Data.Map.Strict as Map
import Data.Text.Prettyprint.Doc hiding ( annotate )

import Language.SessionTypes.Common hiding ( Role )
import Language.SessionTypes.Global
import Language.Common.Id
import Language.Common.Subst
import Language.Alg.Syntax
import Language.Alg.Internal.Parser ( St )
import Language.Alg.Internal.TcM
import Language.Alg.Internal.Ppr
import Language.Par.Role
import Language.Par.Term
import Language.Par.Type
import Language.Par.Prog

data SEnv t = SEnv { fstE :: !(Env (Func t))
                   , sndE :: !(Env (Type t))
                   }

typecheck :: Prim v t => St t -> Prog t v -> IO (TcSt t, TyEnv t, AProg t v)
typecheck st p = go >>= \((e, p'), tcst) -> return (tcst, e, p')
  where
    go = runTcM st $ do
      !(te, pr) <- checkProg p
      !pr' <- rewrite pr
      return (te, pr')

-- Fills in metavar & type information
checkProg :: Prim v t => Prog t v -> TcM t (TyEnv t, Map Id (Alg t v, RwStrat t v))
checkProg = foldM' go (Map.empty, Map.empty) . getDefns
  where
    go (e, ls) (EPar i s2)
      | Just (a, s1) <- Map.lookup i ls = pure (e, Map.insert i (a, rwSeq s1 s2) ls)
      | otherwise = fail $! "Undefined term: " ++ render i
    go (e, f) d = do
      !x <- checkDef d
      case x of
        Left  (i, df) -> let !l = Map.insert i df e in pure (l, f)
        Right (i, a)  -> let !l = Map.insert i (a, RwRefl) f in pure (e, l)

checkDef :: Prim v t => Def t v -> TcM t (Either (Id, TyDef t) (Id, Alg t v))
checkDef (FDef v f) = checkKind Set.empty f *> newPoly v f
                      *> pure (Left (v, AnnF f))
checkDef (TDef v f) = checkKind Set.empty f *> newType v f
                      *> pure (Left (v, AnnT f))
checkDef (Atom v t) = checkKind Set.empty t *> newFun v (ForAll Set.empty t)
                      *> pure (Left (v, AnnA t))
checkDef (EDef i s f) = do
  checkKind (scVars s) (scType s)
  !sb <- typeOf (SEnv emptySubst emptySubst) f (scType s)
  newFun i s
  return $! Right $! (i, subst (fstE sb) f)
checkDef (EPar _i _s) = fail "Unimplemented: checking rewriting strategies"


tcTerm :: Prim v t => Alg t v -> Type t -> TcM t (Env (Type t))
tcTerm e t = typeOf (SEnv Map.empty Map.empty) e t >>= return . sndE

-- FIXME: Refactor, use StateT for typeOf with environments, or (since metavars are
-- introduced fresh), just add Env (Type t) to state. However, there is no need to
-- keep environment of metavars after typechecking definition!
typeOf :: Prim v t => SEnv t -> Alg t v -> Type t -> TcM t (SEnv t)
typeOf s (Var x      ) t
  = lookupVar x >>= skolemise >>= (`unif` t)
  where unif = unify s
typeOf s (Val v      ) t
  = getType (sndE s) v >>= (unify s t . TPrim)
typeOf s (Const e    ) t
  = do !t1 <- TMeta <$!> fresh
       !t2 <- TMeta <$!> fresh
       !s' <- unify s t (t1 `tFun` t2)
       typeOf s' e t2
typeOf s (Unit       ) t
  = unify s t TUnit
typeOf s (Comp es    ) t
  = do !dom <- TMeta <$!> fresh
       !cod <- TMeta <$!> fresh
       !s' <- unify s t (dom `tFun` cod)
       go s' es dom cod
  where
    go _  []     _d _c = error $! "Panic! Empty composition"
    go s0 [e]     d  c = typeOf s0 e (d `tFun` c)
    go s0 (x:xs)  d  c = do
      !ti <- TMeta <$!> fresh
      !s1 <- typeOf s0 x (ti `tFun` c)
      go s1 xs d ti
typeOf s (Id         ) t = do
  !t1 <- TMeta <$!> fresh
  unify s t (t1 `tFun` t1)
typeOf s (Proj i     ) t = do
  !ts <- mapM (const (TMeta <$!> fresh)) [0..i]
  !m  <- Just <$!> fresh
  unify s t (tFun (TPrd ts m) $! last ts)
typeOf s e@(Split es   ) t
  | length es < 2 = fail $! "Ill-formed split: " ++ render e
  | otherwise = do
      !ti  <- TMeta <$!> fresh
      !ts  <- mapM (const (TMeta <$!> fresh)) es
      !s'  <- unify s t (ti `tFun` TPrd ts Nothing)
      foldM' ( uncurry . typeOf) s' $! zip es $! map (tFun ti) ts
typeOf s (Inj  i     ) t = do
  !ts <- mapM (const (TMeta <$!> fresh)) [0..i]
  !m  <- Just <$!> fresh
  unify s t (tFun (last ts) (TSum ts m))
typeOf s e@(Case es   ) t
  | length es < 2 = fail $! "Ill-formed case: " ++ render e
  | otherwise = do
      !ts  <- mapM (const (TMeta <$!> fresh)) es
      !to  <- TMeta <$!> fresh
      !s'  <- unify s t (TSum ts Nothing `tFun` to)
      foldM' (uncurry . typeOf) s' $! zip es $! map (`tFun` to) ts
typeOf s (Fmap f e   ) t = do
  !a <- TMeta <$!> fresh
  !b <- TMeta <$!> fresh
  !s' <- unify s t (TApp f a `tFun` TApp f b)
  typeOf s' e (a `tFun` b)
typeOf s (In f       ) t =
  unify s t $! TApp f (TRec f) `tFun` TRec f
typeOf s (Out f      ) t =
  unify s t $! TRec f `tFun` TApp f (TRec f)
typeOf s (Rec f e1 e2) t = do
  !a <- TMeta <$!> fresh
  !b <- TMeta <$!> fresh
  !s'  <- unify s t (a `tFun` b)
  !s'' <- typeOf s' e2 (a `tFun` TApp f a)
  typeOf s'' e1 (TApp f b `tFun` b)

unifyPoly :: (Eq t, Pretty t, IsCompound t)
          => SEnv t
          -> Func t
          -> Func t
          -> TcM t (SEnv t)
unifyPoly s p          x@(PMeta i)
  | i `Set.member` metaVars p = fail $! "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render p ++ "'"
  | Just p' <- Map.lookup i (fstE s) = unifyPoly s p p'
  | otherwise = pure $! (SEnv (Map.insert i p $! fstE s) $! sndE s)
unifyPoly s x@PMeta{}  p = unifyPoly s p x
unifyPoly s (PPrd ps1) (PPrd ps2) = foldM' (uncurry . unifyPoly) s $! zip ps1 ps2
unifyPoly s (PSum ps1) (PSum ps2) = foldM' (uncurry . unifyPoly) s $! zip ps1 ps2
unifyPoly s (PK t1)    (PK t2)    = unify s t1 t2
unifyPoly s t1    t2
  | t1 == t2   = return s
  | otherwise = fail $! "Cannot unify '" ++ render (subst (sndE s) t1)
                ++ "' with '" ++ render (subst (sndE s) t2) ++ "'"
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
    (l, JRight r) -> let !(ll, lr) = last l
                    in init l ++ [(ll, TFun $! lr:r)]
    (l, JLeft  r) -> let !(ll, lr) = last l
                    in init l ++ [(TFun $! ll:r, lr)]

unify :: (Eq t, Pretty t, IsCompound t) => SEnv t -> Type t -> Type t -> TcM t (SEnv t)
unify s@(SEnv fe se) t x@(TMeta i)
  | Just t' <- Map.lookup i se  = unify s t t'
  | i `Set.member` metaVars t = fail $! "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render t ++ "'"
  | otherwise                 = pure $! (SEnv fe (Map.insert i t se))
unify s x@TMeta{} t = unify s t x
unify s0 (TFun ts1) (TFun ts2) = foldM' (uncurry . unify) s0 $! zipF ts1 ts2
unify s0 t1@(TSum ts1 mii) t2@(TSum ts2 mjj)
  = do !s1 <- foldM' (uncurry . unify) s0 ts
       unifyTail msge TSum s1 m mii mjj
  where
    !(ts, m) = zipD ts1 ts2
    msge _ = "Cannot unify sum '" ++ render t1
              ++ "' with '" ++ render t2 ++ "'"
unify s0 t1@(TPrd ts1 mii) t2@(TPrd ts2 mjj)
  = do !s1 <- foldM' (uncurry . unify) s0 ts
       unifyTail msge TPrd s1 m mii mjj
  where
    !(ts, m) = zipD ts1 ts2
    msge s' = "Cannot unify prod '" ++ render (subst s' t1)
              ++ "' with '" ++ render (subst s' t2) ++ "'"
unify s0 (TApp f1 t1) (TApp f2 t2) = do
  !s1 <- unifyPoly s0 f1 f2
  unify s1 t1 t2
unify s0 (TApp f1 t1) t2 = do
  !t1' <- appPoly (substPoly (fstE s0) f1) t1
  unify s0 t1' t2
unify s0 t2 (TApp f1 t1) = do
  !t1' <- appPoly (substPoly (fstE s0) f1) t1
  unify s0 t2 t1'
unify s0 (TRec f1) (TRec f2) = do
  unifyPoly s0 f1 f2
unify s t1 t2
  | t1 == t2   = pure s
  | otherwise = fail $! "Cannot unify type '" ++ render (subst (sndE s) t1)
                ++ "' with '" ++ render (subst (sndE s) t2) ++ "'"

-- Unify products/sums with different num of elements
unifyTail :: (Eq t, Pretty t, IsCompound t)
          => (Env (Type t) -> String)
          -> ([Type t] -> Maybe Int -> Type t)
          -> SEnv t
          -> MEither [Type t] [Type t]
          -> Maybe Int
          -> Maybe Int
          -> TcM t (SEnv t)
unifyTail _      _   s None Nothing  Nothing  = return $! s
unifyTail _      spr s None (Just i) mj       = unify s (spr [] mj) (TMeta i)
unifyTail _      spr s None mi (Just j)       = unify s (spr [] mi) (TMeta j)
unifyTail _      spr s (JLeft l) mi (Just j)  = unify s (spr l  mi) (TMeta j)
unifyTail msgerr _   s (JLeft _) _  Nothing   = fail (msgerr $! sndE s)
unifyTail _      spr s (JRight l) (Just i) mj = unify s (spr l  mj) (TMeta i)
unifyTail msgerr _   s (JRight _) Nothing  _  = fail (msgerr $! sndE s)

appPoly :: Pretty t => Func t -> Type t -> TcM t (Type t)
appPoly (PK t)    _ = pure t
appPoly (PV v)    t = lookupPoly v >>= (`appPoly` t)
appPoly PI        t = pure t
appPoly (PPrd ps) t = TPrd <$!> mapM (`appPoly` t) ps <*> pure Nothing
appPoly (PSum ps) t = TSum <$!> mapM (`appPoly` t) ps <*> pure Nothing
appPoly x@PMeta{} t = fail $! "Ambiguous type '" ++ render (TApp x t) ++ "'"

--------------------------------------------------------------------------------
-- REWRITER

rewrite :: Prim v t => Map Id (Alg t v, RwStrat t v) -> TcM t (AProg t v)
rewrite defns = mapM rwStrat $! Map.toList toRewrite
  where
    !toRewrite = Map.filter notRefl defns
    notRefl (_, RwRefl) = False
    notRefl _           = True

rwStrat ::  Prim v t => (Id, (Alg t v, RwStrat t v)) -> TcM t (ADef t v)
rwStrat (i, (ef, rw)) = do
  !sc <- lookupVar i
  case scType sc of
    TFun (a:_) -> do
      let initR = Rol 0
          initT = TyAnn a $! initR
      !af <- rwAlg rw (AnnAlg ef initR)
      -- !aty <- roleInfer a initR
      !(aty, gg) <- protoInfer initT af
      return $! AnnEDef i (AForAll (scVars sc) (TyAnn a (Rol 0)) aty) af gg
    _ -> fail $! "The definition '" ++ render i ++ "' is not a function."

rwAlg :: Prim v t => RwStrat t v -> ATerm t v -> TcM t (ATerm t v)
rwAlg (RwSeq s1 s2) a = rwAlg s1 a >>= rwAlg s2
rwAlg RwRefl        a = pure a
rwAlg (Unroll i) (AnnAlg (Rec f m s) r1) = do
  rf <- (`AnnAlg` r1) <$!> unroll f m s i
  pure rf
rwAlg Unroll{} t = fail $! "Cannot unroll: " ++ render t
rwAlg (Annotate s) ef = go ef
  where
    go (AnnAlg e r) = do
      a <- annotate r s e
      pure a
    go a = fail $ "Cannot annotate. Already annotated: " ++ render a


--------------------------------------------------------------------------------
-- PROTOCOLS AND ROLES

rAnn :: (Eq t, Pretty t) => Type t -> Role -> Either [Char] (AType t)
rAnn t (RId i)
  = pure $! TyAnn t i
rAnn t (RAlt rs)
  = tyAlt <$!> mapM (rAnn t) rs
rAnn (TSum ts _) (RBrn i r) | len > i
  = TyBrn i len <$!> rAnn (ts !! i) r
  where
    !len = length ts
rAnn (TPrd ts _) (RPrd rs)
  | length ts == length rs
  = TyPrd <$!> zipWithM rAnn ts rs
rAnn l r
  = Left $ "Cannot annotate type '" ++ render l ++ "' with '" ++ render r ++ "'"

rGet :: (Eq a, Pretty a, IsCompound a)
     => AType a
     -> TcM a (Role, Type a)
rGet (TyAnn t i) = pure (RId i, t)
rGet (TyBrn i _ a) = do
  ts <- mapM (const (TMeta <$> fresh)) [0..i-1]
  n <- fresh
  (r, t) <- rGet a
  pure (RBrn i r, TSum (ts ++ [t]) $ Just n)
rGet (TyAlt []) = error $ "Panic! empty alternative in 'rGet'"
rGet (TyAlt (x:xs)) = do
  (r , t) <- rGet x
  (rs, ts) <- unzip <$!> mapM rGet xs
  sb <- foldM' (`unify` t) (SEnv Map.empty Map.empty) $! ts
  pure (RAlt $ r : rs, subst (sndE sb) t)
rGet (TyPrd xs) = do
  (rs, ts) <- unzip <$!> mapM rGet xs
  pure $! (RPrd rs, TPrd ts Nothing)
rGet (TyApp f r t) = pure $! (r, TApp f t)
rGet TyMeta{} = error $ "Panic, ambiguous annotated type!"

-- Pre: ATerm must be well-typed, and role match its input type.
roleTrack :: ATerm t v -> Role -> Role
roleTrack p (RAlt ts)   = RAlt $! map (roleTrack p) ts
roleTrack AnnId t        = t
roleTrack (AnnAlg _ r) _ = RId r
roleTrack (AnnComp es) t = go (reverse es) t
  where
    go l (RAlt (th : ts))
      | all (== th) ts = go l th
    go [] t' = t'
    go (x:xs) t' = go xs $! roleTrack x t'
roleTrack (AnnPrj i) (RPrd ts) = ts !! (fromInteger i)
roleTrack (AnnPrj _) r = r
roleTrack (AnnSplit es) t = RPrd $! map (`roleTrack` t) es
roleTrack (AnnCase es) (RBrn i a)
  = let !e = es !! i
    in roleTrack e a
roleTrack (AnnCase es) r
  = rAlt $! map (`roleTrack` r) es
roleTrack (AnnInj i) t
  = RBrn (fromInteger i) t
roleTrack _ _
  = error $! "Panic! Ill-typed term reached "

tyAlt :: Eq t => [AType t] -> AType t
tyAlt (t:ts)
  | all (== t) ts = t
tyAlt ts = TyAlt ts

tryChoice :: AType t -> Maybe (RoleId, [AType t])
tryChoice (TyAnn (TSum ts _) r)
  = Just (r, zipWith (`TyBrn` len) [0..] $! map (`TyAnn` r) ts)
  where
    !len = length ts
tryChoice (TyBrn i j t)
  | Just (r, ts) <- tryChoice t
  = Just (r, map (TyBrn i j) ts)
tryChoice (TyPrd ts)
  | Just (r, ts1) <- go ts = Just (r, map TyPrd ts1)
  where
    go [] = Nothing
    go (x : xs)
      | Just (r, bs) <- tryChoice x = Just (r, map (:xs) bs)
      | Just (r, xs') <- go xs = Just (r, map (x:) xs')
      | otherwise = Nothing
tryChoice _ = Nothing

protocol :: Prim v t => AnnScheme t -> ATerm t v -> TcM t (Global t)
protocol sc t = snd <$> protoInfer (ascDom sc) t

protoInfer :: forall t v. Prim v t => AType t -> ATerm t v -> TcM t (AType t, Global t)

--      A_i |= p ~ G_i : B_i
--      -----------------------------------------------------
--      A_1 \oplus A_2 |= p ~ G_1 \oplus G_2 : B_1 \oplus B_2
protoInfer (TyAlt as) p = do
  (bs, ps) <- unzip <$!> mapM (`protoInfer` p) as
  pure $! (tyAlt bs, Brn ps)
-- Post : all rules A |= p ~ G : B from now on can assume A is not A_1 \oplus A_2,
-- so G must be a single global type, not a global type branch!

protoInfer a p = do
  (b, t) <- inferGTy a p
  pure (b, Leaf t)

requiresChoice :: RoleId -> AType t -> ATerm t v -> Bool
requiresChoice r (TyAnn _ r') (AnnCase _)
  | r == r' = True
requiresChoice r a (AnnComp es ) = any (requiresChoice r a) es
requiresChoice r a (AnnSplit es) = any (requiresChoice r a) es
requiresChoice _ _ _ = False

inferGTy :: forall t v. Prim v t => AType t -> ATerm t v -> TcM t (AType t, GTy t)

inferGTy (TyAnn (TApp f a) r) p =
  appPoly f a >>= \b -> inferGTy (TyAnn b r) p
-- Early choice:
--
--      A ~>^r Sum A_i       A_i |= p ~ G_i : B_i
--      -----------------------------------------------------
--      A |= p ~ G_1 \oplus G_2 : B_1 \oplus B_2
inferGTy a p
  | Just (r, as) <- tryChoice a, requiresChoice r a p = do
  (bs, gs) <- unzip <$!> mapM (`inferGTy` p) as
  let !g  = Choice r rs $! foldr (uncurry addAlt) emptyAlt $! zip [0..] gs
      !rs = Set.toList $! r `Set.delete` (typeRoles a `Set.union` termRoles p)
  pure $! (tyAlt bs, g)
-- Post: no role contains sum types

-- Message
inferGTy a (AnnAlg e r) = do
  !ty <- TMeta <$!> fresh
  !(_, ti) <- rGet a -- Metavariables in branches should not be used in return
                    -- type, we are not in a choice here!
  !s  <- tcTerm e (ti `tFun` ty)
  let !ty' = subst s ty

  g <- msg a r
  pure (TyAnn ty' r, g GEnd)

-- Identity
inferGTy a AnnId = pure (a, GEnd)

-- Composition
inferGTy a (AnnComp es) = go $ reverse es
  where
    go [] = pure (a, GEnd)
    go (p:ps) = do
      (t , g)  <- aux (length ps > 0) p
      (t', gb) <- protoInfer t (AnnComp $! reverse ps)
      pure (t', seqG g gb)
    aux True (AnnSplit ts) = dupBranches a ts
    aux _     p = inferGTy a p


-- Projection
inferGTy (TyAnn (TPrd ts _) r) (AnnPrj i)
  | n < length ts = pure (TyAnn (ts !! n) r, GEnd)
  where
    n = fromInteger i
inferGTy (TyPrd ts) (AnnPrj i)
  | n < length ts = pure (ts !! n, GEnd)
  where
    n = fromInteger i
inferGTy _ AnnPrj{}
  | otherwise     = fail "Typecheck.inferGTy: ill-typed term in projection"

-- Split
inferGTy a (AnnSplit es) = do
  (rs, gs) <- unzip <$!> mapM (inferGTy a) es
  pure $ (TyPrd rs, gSeq gs)
  --let !t  = liftPrd rs
  --    !g  = seqChoices gs
  --pure $ (t, g)
  --where
  --  liftPrd []     = TyPrd [] -- XXX: should never happen
  --  liftPrd (t:ts) = goP ts [] t

  --  goP ts ps (TyAlt rs) = TyAlt $ map (goP ts ps) rs
  --  goP []     ps t      = TyPrd (t : ps)
  --  goP (t:ts) ps p      = goP ts (p : ps) t

  --  seqChoices []     = GEnd
  --  seqChoices (g:gs) = goG gs g

  --  goG [] g = g
  --  goG l@(g1:gs) g =
  --    case g of
  --      Choice r rs alts
  --        -> Choice r rs $! mapAlt (\ _ g2 -> gSeq [g2, goG gs g1]) alts
  --      Comm m gn -> Comm m $! goG l gn
  --      GRec r gn -> GRec r $! goG l gn
  --      GSeq gl   -> gSeq [GSeq (init gl), goG l (last gl)]
  --      GVar v    -> GVar v
  --      GEnd      -> goG gs g1

-- Split
inferGTy a (AnnInj i) =
  pure (tagAlts (fromInteger i) a, GEnd)
  where
    tagAlts j (TyAlt ts) = tyAlt $! map (tagAlts j) ts
    tagAlts j b = TyBrn j (-1) b

-- Case
inferGTy (TyBrn i _ a) (AnnCase ps)
  | length ps > i = inferGTy a (ps !! i)
inferGTy r AnnCase{}
  = fail $! "Typecheck.inferGTy reached case expression in an un-tagged role: "
    ++ render r

inferGTy _ AnnFmap{}
  = fail $ "Unimplemented"


needBranch :: (Pretty t, Eq t, IsCompound t) => [AType t] -> TcM t Int
needBranch ts = do
  (ri, _) <- unzip <$!> mapM rGet ts
  return $! go 0 ri
  where
    go i (r : rsn) =
      case getAlts r of
        (r1 : rs1)
          | all (r1 ==) $ rs1 -> go (i+1) rsn
          | otherwise -> i
        _ -> go (i+1) rsn
    go i [] = i
    getAlts (RAlt rs) = concatMap getAlts rs
    getAlts r = [r]


dupBranches :: forall t v. Prim v t => AType t -> [ATerm t v] -> TcM t (AType t, GTy t)
dupBranches a es = do
  (rs, gs) <- unzip <$!> mapM (inferGTy a) es
  i <- needBranch rs
  let r1 = take i rs
      rs2 = drop i rs
      g1 = take i gs
      gs2 = drop i gs
      !t = liftPrd r1 rs2
      !g = seqChoices g1 gs2
  pure $ (t, g)
  where
    liftPrd r1 []     = TyPrd r1 -- XXX: should never happen
    liftPrd r1 (t:ts) = goP ts r1 t

    goP ts ps (TyAlt rs) = tyAlt $ map (goP ts ps) rs
    goP []     ps t      = TyPrd (t : ps)
    goP (t:ts) ps p      = goP ts (p : ps) t

    seqChoices g1 []     = gSeq g1
    seqChoices g1 (g:gs) = gSeq $ g1 ++ [goG gs g]

    goG [] g = g
    goG l@(g1:gs) g =
      case g of
        Choice r rs alts
          -> Choice r rs $! mapAlt (\ _ g2 -> gSeq [g2, goG gs g1]) alts
        Comm m gn -> Comm m $! goG l gn
        GRec r gn -> GRec r $! goG l gn
        GSeq gl   -> gSeq [GSeq (init gl), goG l (last gl)]
        GVar v    -> GVar v
        GEnd      -> goG gs g1



-- Pre: no sum types, no alts
msg :: Pretty t => AType t -> RoleId -> TcM t (GTy t -> GTy t)
msg (TyAnn t  ri   ) ro
  | ri == ro = pure id
  | otherwise = comm
  where
    comm = pure $! Comm (Msg [ri] [ro] t Nothing)
msg (TyBrn _ _ a) ro = msg a ro
msg (TyPrd ts   ) ro = foldl' (.) id <$!> mapM (`msg` ro) ts
msg t@TyAlt{}     _  = fail $! "Typecheck.msg: Found type alternative: " ++ render t
msg t@TyApp{}     _  = fail $! "Typecheck.msg: Found functor application: " ++ render t
msg t@TyMeta{}    _  = fail $! "Typecheck.msg: Ambiguous annotated type: " ++ render t

seqG :: Pretty t => GTy t -> Global t -> GTy t
seqG (Choice r rs gs1) g@(Brn g2)
  = Choice r lrs $! mapAlt (\ (Lbl l) gt -> seqG gt (g2 !! l)) gs1
  where
    !rs' = Set.fromList rs `Set.union` gRoles g Set.\\ Set.singleton r
    !lrs = Set.toList rs'
seqG c@Choice{}      (BSeq gs g)    = gSeq $! (seqG c $ Brn gs) : g
seqG (Comm m g1)     g2             = Comm m $! seqG g1 g2
seqG (GRec v g1)     g2             = GRec v $! seqG g1 g2
seqG g@GVar{}        _              = g
seqG GEnd            (Leaf g2)      = g2
seqG g1              (Leaf g2)      = gSeq $! [g1, g2]
seqG g1              g2             = error (m ++ "\n" ++ render g1 ++ "\n\n" ++ render g2)
  where
    m = "Panic! Ill-formed sequencing of \
        \global types in Language.Alg.Typecheck.seqG"

gSeq :: [GTy t] -> GTy t
gSeq ls =
  case  filter notEnd ls of
    [] -> GEnd
    [x] -> x
    (Comm i g1 : gs) -> Comm i $! gSeq $ g1 : gs
    ls' -> GSeq ls'
  where
    notEnd GEnd = False
    notEnd _    = True
