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
  , protocol
  , checkProg
  , checkDef
  , tcTerm
  , execTcM
  , appPoly
  ) where

import Control.Arrow ( (***) )
import Control.Monad ( zipWithM )
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad ( foldM, (<=<) )
import Data.Text.Prettyprint.Doc hiding ( annotate )

import Language.SessionTypes.Common
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

type SEnv t = (Env (Func t), Env (Type t))

typecheck :: Prim v t => Int -> St t -> Prog t v -> IO (TcSt t, TyEnv t, AProg t v)
typecheck d st = (\((e, p), tcst) -> return (tcst, e, p))
               <=< (go . checkProg)
  where
    go = runTcM d st

-- Fills in metavar & type information
checkProg :: Prim v t => Prog t v -> TcM t (TyEnv t, AProg t v)
checkProg = (\(a, b) -> pure (a, reverse b)) <=< foldM go (Map.empty, []) . getDefns
  where
    go (e, ls) d = do
      x <- checkDef d
      case x of
        Left (i, df) -> pure (Map.insert i df e, ls)
        Right l     -> pure (e, l : ls)

checkDef :: Prim v t => Def t v -> TcM t (Either (Id, TyDef t) (ADef t v))
checkDef (FDef v f) = checkKind Set.empty f *> newPoly v f
                      *> pure (Left (v, AnnF f))
checkDef (TDef v f) = checkKind Set.empty f *> newType v f
                      *> pure (Left (v, AnnT f))
checkDef (Atom v t) = checkKind Set.empty t *> newFun v (ForAll Set.empty t)
                      *> pure (Left (v, AnnA t))
checkDef (EDef i s f) = do
  checkKind (scVars s) (scType s)
  sb <- typeOf (emptySubst, emptySubst) f (scType s)
  newFun i s
  af <- annotate $ subst (fst sb) f
  case scType s of
    TFun (a:_) -> do
      aty <- roleInfer af (TyAnn a (Rol 0))
      gg <- protoInfer (TyAnn a (Rol 0)) af
      return $ Right $ AnnEDef i (AForAll (scVars s) (TyAnn a (Rol 0)) aty) af gg
    _ -> fail $ "The definition '" ++ render i ++ "' is not a function."


tcTerm :: Prim v t => Alg t v -> Type t -> TcM t (Env (Type t))
tcTerm e t = typeOf (Map.empty, Map.empty) e t >>= return . snd

-- FIXME: Refactor, use StateT for typeOf with environments, or (since metavars are
-- introduced fresh), just add Env (Type t) to state. However, there is no need to
-- keep environment of metavars after typechecking definition!
typeOf :: Prim v t => SEnv t -> Alg t v -> Type t -> TcM t (SEnv t)
typeOf s (Var x      ) t
  = lookupVar x >>= skolemise >>= (`unif` t)
  where unif = unify s
typeOf s (Val v      ) t
  = getType (snd s) v >>= (unify s t . TPrim)
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
      s1 <- typeOf s0 x (ti `tFun` c)
      go s1 xs d ti
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

unifyPoly :: (Eq t, Pretty t, IsCompound t)
          => SEnv t
          -> Func t
          -> Func t
          -> TcM t (SEnv t)
unifyPoly s p          x@(PMeta i)
  | i `Set.member` metaVars p = fail $ "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render p ++ "'"
  | Just p' <- Map.lookup i (fst s) = unifyPoly s p p'
  | otherwise = pure $ (Map.insert i p $ fst s, snd s)
unifyPoly s x@PMeta{}  p = unifyPoly s p x
unifyPoly s (PPrd ps1) (PPrd ps2) = foldM (uncurry . unifyPoly) s $ zip ps1 ps2
unifyPoly s (PSum ps1) (PSum ps2) = foldM (uncurry . unifyPoly) s $ zip ps1 ps2
unifyPoly s (PK t1)    (PK t2)    = unify s t1 t2
unifyPoly s t1    t2
  | t1 == t2   = return s
  | otherwise = fail $ "Cannot unify '" ++ render (subst (snd s) t1)
                ++ "' with '" ++ render (subst (snd s) t2) ++ "'"
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

unify :: (Eq t, Pretty t, IsCompound t) => SEnv t -> Type t -> Type t -> TcM t (SEnv t)
unify s t x@(TMeta i)
  | Just t' <- Map.lookup i (snd s)  = unify s t t'
  | i `Set.member` metaVars t = fail $ "Occurs check, cannot unify '"
                                ++ render x ++ "' with '" ++ render t ++ "'"
  | otherwise                 = pure $ (id *** Map.insert i t) s
unify s x@TMeta{} t = unify s t x
unify s0 (TFun ts1) (TFun ts2) = foldM (uncurry . unify) s0 $ zipF ts1 ts2
unify s0 t1@(TSum ts1 mii) t2@(TSum ts2 mjj)
  = do s1 <- foldM (uncurry . unify) s0 ts
       unifyTail msge TSum s1 m mii mjj
  where
    (ts, m) = zipD ts1 ts2
    msge _ = "Cannot unify sum '" ++ render t1
              ++ "' with '" ++ render t2 ++ "'"
unify s0 t1@(TPrd ts1 mii) t2@(TPrd ts2 mjj)
  = do s1 <- foldM (uncurry . unify) s0 ts
       unifyTail msge TPrd s1 m mii mjj
  where
    (ts, m) = zipD ts1 ts2
    msge s' = "Cannot unify prod '" ++ render (subst s' t1)
              ++ "' with '" ++ render (subst s' t2) ++ "'"
unify s0 (TApp f1 t1) (TApp f2 t2) = do
  s1 <- unifyPoly s0 f1 f2
  unify s1 t1 t2
unify s0 (TApp f1 t1) t2 = do
  t1' <- appPoly (substPoly (fst s0) f1) t1
  unify s0 t1' t2
unify s0 t2 (TApp f1 t1) = do
  t1' <- appPoly (substPoly (fst s0) f1) t1
  unify s0 t2 t1'
unify s0 (TRec f1) (TRec f2) = do
  unifyPoly s0 f1 f2
unify s t1 t2
  | t1 == t2   = pure s
  | otherwise = fail $ "Cannot unify type '" ++ render (subst (snd s) t1)
                ++ "' with '" ++ render (subst (snd s) t2) ++ "'"

-- Unify products/sums with different num of elements
unifyTail :: (Eq t, Pretty t, IsCompound t)
          => (Env (Type t) -> String)
          -> ([Type t] -> Maybe Int -> Type t)
          -> SEnv t
          -> MEither [Type t] [Type t]
          -> Maybe Int
          -> Maybe Int
          -> TcM t (SEnv t)
unifyTail _      _   s None Nothing  Nothing  = return s
unifyTail _      spr s None (Just i) mj       = unify s (spr [] mj) (TMeta i)
unifyTail _      spr s None mi (Just j)       = unify s (spr [] mi) (TMeta j)
unifyTail _      spr s (JLeft l) mi (Just j)  = unify s (spr l  mi) (TMeta j)
unifyTail msgerr _   s (JLeft _) _  Nothing   = fail (msgerr $ snd s)
unifyTail _      spr s (JRight l) (Just i) mj = unify s (spr l  mj) (TMeta i)
unifyTail msgerr _   s (JRight _) Nothing  _  = fail (msgerr $ snd s)

appPoly :: Pretty t => Func t -> Type t -> TcM t (Type t)
appPoly (PK t)    _ = pure t
appPoly (PV v)    t = lookupPoly v >>= (`appPoly` t)
appPoly PI        t = pure t
appPoly (PPrd ps) t = TPrd <$> mapM (`appPoly` t) ps <*> pure Nothing
appPoly (PSum ps) t = TSum <$> mapM (`appPoly` t) ps <*> pure Nothing
appPoly x@PMeta{} t = fail $ "Ambiguous type '" ++ render (TApp x t) ++ "'"

-- p |- A -> B, where A is given, infer B
roleInfer :: Prim v t => ATerm t v -> AType t -> TcM t (AType t)
roleInfer p (TyAlt ts)   = TyAlt <$> mapM (roleInfer p) ts
roleInfer AnnId t        = pure t
roleInfer (AnnAlg e r) t = do
  ty <- TMeta <$> fresh
  let (ri, ti) = rGet t
  s  <- tcTerm e (ti `tFun` ty)
  return $ addBranch ri $ TyAnn (subst s ty) r
roleInfer (AnnComp es) t = go (reverse es) t
  where
    go [] t' = pure t'
    go (x:xs) t' = roleInfer x t' >>= go xs
roleInfer p@(AnnPrj i) (TyPrd ts)
  | length ts > (fromInteger i)
  = pure $ ts !! (fromInteger i)
  | otherwise
  = fail $ "Cannot infer annotated type of '" ++ render p ++ "'"
roleInfer p@(AnnPrj i) (TyAnn (TPrd ts _) r)
  | length ts > (fromInteger i)
  = pure $ TyAnn (ts !! (fromInteger i)) r
  | otherwise
  = fail $ "Cannot infer annotated type of '" ++ render p ++ "'"
roleInfer (AnnSplit es) t
  = prodAlt [] <$> mapM (`roleInfer` t) es
  where
    prodAlt l [] = TyPrd $ reverse l
    prodAlt l (TyAlt ti : ts) = TyAlt (map (\ tin -> prodAlt l (tin : ts)) ti)
    prodAlt l (to : ts) = prodAlt (to : l) ts
roleInfer (AnnCase es) (TyBrn i _ a _)
  = roleInfer (es !! i) a
roleInfer (AnnCase es) (TyAnn (TSum ts _) r)
  = TyAlt <$> mapM (\ (e, t) -> roleInfer e (TyAnn t r)) (zip es ts)
roleInfer (AnnInj i) t
  = do vs <- mapM (const (TMeta <$> fresh)) [0..i-1]
       v <- fresh
       pure $ TyBrn (fromInteger i) vs t (Left v) -- XXX: generate metavars!!!
roleInfer AnnFmap{} _
  = error "Panic! fmap should be unrolled before reaching this point"
roleInfer e (TyAnn (TApp f a) r)
  = appPoly f a >>= \b -> roleInfer e (TyAnn b r)
roleInfer e t
  = fail $ "Cannot type-check '" ++ render e ++ "' against annotated type '" ++
    render t ++ "'"

infixl 4 |>

(|>) :: Pretty t => GTy t -> Global t -> String -> GTy t
Choice r rs gs1 |> g@(Brn g2)
  = \ctx -> Choice r (Set.toList rs') $ mapAlt (\ (Lbl l) gt -> (gt |> g2 !! l) ctx) gs1
  where
    rs' = Set.fromList rs `Set.union` gRoles g Set.\\ Set.singleton r
Comm m g1       |> g2          = \ctx -> Comm m $ (g1 |> g2) ctx
GRec v g1       |> g2          = \ctx -> GRec v $ (g1 |> g2) ctx
g@GVar{}        |> _           = \_tx -> g
GEnd            |> Leaf g2     = \_tx -> g2
l               |> r           = \ctx -> error (m ctx)
  where
    m ctx = "Panic! Ill-formed sequencing of \
        \global types in Language.Alg.Typecheck.|>, called from " ++ ctx ++ "\n\n"
        ++ render l ++ "\n" ++ render r

seqP :: Pretty t => String -> Global t -> Global t -> Global t
seqP ctx (Leaf g1)  g2       = Leaf $ (g1 |> g2) ctx
seqP ctx (Brn gs1) (Brn gs2) = Brn $ zipWith (seqP ctx) gs1 gs2
seqP ctx l        r          = error m
  where
    m = "Panic! Ill-formed sequencing of \
        \global types in Language.Alg.Typecheck.seqP called from " ++ ctx ++ "\n\n"
        ++ render l ++ "\n" ++ render r

msg :: Pretty t => AType t -> RoleId -> TcM t (Global t)
msg (TyAnn t ri   ) ro = Leaf <$> comm
  where
    comm = Comm <$> pure (Msg [ri] [ro] t ()) <*> pure GEnd
msg (TyBrn _ _ a _) ro = msg a ro
msg (TyAlt ts     ) ro = Brn <$> mapM (`msg` ro) ts
msg t@(TyPrd ts   ) ro = foldr1 (seqP $ "msg:" ++ render t) <$> mapM (`msg` ro) ts
msg t@TyApp{}       _  = fail $ "Found functor application: " ++ render t
msg (TyMeta i)      _  = fail $ "Ambiguous annotated type" ++ render i

protocol :: Prim v t => AnnScheme t -> ATerm t v -> TcM t (Global t)
protocol sc t = protoInfer (ascDom sc) t

protoInfer :: forall t v. Prim v t => AType t -> ATerm t v -> TcM t (Global t)

protoInfer (TyAnn (TApp f a) ri) e
  = appPoly f a >>= \b -> protoInfer (TyAnn b ri) e

protoInfer ti    (AnnComp es ) = go (reverse es) ti
  where
    go [] t = protoInfer t (AnnId :: ATerm t v)
    go (e:es') t = do
      g  <- protoInfer t e
      tn <- roleInfer e t
      gg <- go es' tn
      seqP ("protoInfer: comp: left: "
            ++ render e
            ++ "\n\n right:"
            ++ render (AnnComp es')
            ++ "\n\n type in:"
            ++ render t
            ++ "\n\n type next:"
            ++ render tn
            ++ "\n\n global type left \n\t"
            ++ render g
            ++ "\n\n global type right \n\t"
            ++ render gg) <$> protoInfer t e <*> (roleInfer e t >>= go es')
protoInfer ti ei@(AnnSplit es  ) = go (reverse es) ti
  where
    go l (TyAlt ts) = Brn <$> mapM (go l) ts
    go [] t = pure $ repeatAlts t $ Leaf GEnd
    go (e:es') t
      = seqP ("protoInfer: split: " ++ render ei)
      <$> protoInfer t e
      <*> (roleInfer e t >>= \ tn ->
              go es' (multAlts tn t))
protoInfer (TyAnn (TSum ts _) ri) (AnnCase es)
  = do gs <- zipWithM getGT as es
       let rs = Set.toList $ Set.unions (map getRoles gs) Set.\\ Set.singleton ri
       return $ Leaf $ Choice ri rs $ foldr (uncurry addAlt) emptyAlt $ zip [0..] gs
  where
    as = map (`TyAnn` ri) ts
    getGT a e = protoInfer a e >>= \(Leaf i) -> pure i
protoInfer t  p@AnnCase{}     = fail $ "The input to annotated case '"
  ++ render p ++ "' cannot be distributed into annotated type '"
  ++ render t ++ "'"

protoInfer (TyAlt ti) e
  = Brn <$> mapM (\t -> protoInfer t e) ti

protoInfer _  AnnPrj{}        = pure $ Leaf GEnd
protoInfer _  AnnInj{}        = pure $ Leaf GEnd
protoInfer ti (AnnAlg _ r   ) = msg ti r
protoInfer _   AnnId          = pure $ Leaf GEnd
protoInfer _  AnnFmap{}       = fail "Unimplemented"

multAlts :: AType t1 -> AType t2 -> AType t2
multAlts (TyAlt ts) t' = TyAlt $ map (`multAlts` t') ts
multAlts _          t' = t'

repeatAlts :: AType t -> Global t -> Global t
repeatAlts (TyAlt ts) g = Brn $ map (`repeatAlts` g) ts
repeatAlts _          g = g

addBranch :: Language.Par.Role.Role -> AType t -> AType t
addBranch (RAlt  rs) t = TyAlt $ map (`addBranch` t) rs
addBranch (RBrn _ r) t = addBranch r t
addBranch (RPrd  rs) t = foldr (\r t' -> addBranch r t') t rs
addBranch _          t = t