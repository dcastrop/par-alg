{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wwarn #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
-- Endpoint terms: monadic language for parallel programs
module Language.Ept.EMonad
  ( ETerm(..)
  , EFun(..)
  , EMonad(..)
  , EProg(..)
  , cmsg
  , gen
  , genAlt
  , genProg
  , generate
  , renderPCode
  , roleTrack
  , renderPrelude
  ) where

import Control.Arrow ( second )
import Control.Monad.RWS.Strict
import Data.Char ( toUpper )
import Data.Map ( Map )
import Data.Set ( Set )
import Data.List ( scanl' )
import Debug.Trace
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.SessionTypes.Common ( Role(..) )
import Language.SessionTypes.Global
import Language.Common.Id
import Language.Alg.Syntax
import Language.Alg.Typecheck
import Language.Alg.Internal.TcM
import Language.Alg.Internal.Ppr
import Language.Par.Role
import Language.Par.Term
import Language.Par.Type
import Language.Par.Prog

generate :: Prim v t => TcSt t v -> WtProg t v -> IO (Int, EProg t v)
generate tcst p = return (nextVar st, a)
  where
    (a, st, _w) = runRWS (genProg p) () tcst

genProg :: Prim v t => WtProg t v -> TcM t v (EProg t v)
genProg defs = do
  par <- Map.fromList <$!> mapM genDef (wtPDefs defs)
  hsDefs1 <- Map.traverseWithKey (\ i (_, a) -> convertToHs i a) (wtDefs defs)
  hsDefs2 <- (defnsR <$> get) >>= Map.traverseWithKey convertToHs
  pure $! EProg (Map.union hsDefs1 hsDefs2) par
  where
    keep m = sameVar >>= \v -> m <* modify (\st -> st { nextVar = v })
    genDef (AnnEDef f sc p _)
      = case (aty, ascCod sc) of
          (TyAnn _ ri, TyAnn _ ro)
            | ri == ro -> ((f,) . Map.fromList) <$!> mapM genRole rs
          _ -> fail $ "Cannot generate parallel code for function " ++
              render f ++ ". Cannot find a 'master' role."
      where
        genRole r = (r,) <$> (keep (seqAltsF <$!> gen r p aty <*> close r (ascCod sc)))
        aty = ascDom sc
        rs =  Set.toList $! typeRoles aty `Set.union` termRoles p

close :: RoleId -> AType t -> TcM t v (EAlt t v)
close r (TyAlt ts) = ENode <$> mapM (close r) ts
close r (TyBrn i j a)
  | r `Set.member` typeRoles a = ELeaf <$> eAbs sameVar (\x -> mRet (EInj i j x))
close _ _ = ELeaf <$> fId

data ETerm t v
  = EVar !Id
  | EVal !v
  | EUnit
  | EPair ![ETerm t v]
  | EProj !Int !Int !(ETerm t v)
  | EInj !Int !Int !(ETerm t v)
  | ECase !(ETerm t v) ![(Id, ETerm t v)]
  | ELet !Id !(ETerm t v) !(ETerm t v)
  | EApp !Id !(ETerm t v)
  deriving (Show, Eq)

fvsT :: ETerm t v -> Set Id
fvsT (EVar i) = Set.singleton i
fvsT (EPair ts) = Set.unions $ map fvsT ts
fvsT (EInj _ _ t) = fvsT t
fvsT (EProj _ _ t) = fvsT t
fvsT (EApp i t) = Set.insert i $ fvsT t
fvsT (ECase t ls) = Set.union (fvsT t) $ Set.unions (map (fvsT . snd) ls)
                      Set.\\ Set.fromList (map fst ls)

fvsT (ELet v t1 t2) = Set.union (fvsT t1) (fvsT t2 Set.\\ Set.singleton v)
fvsT EUnit = Set.empty
fvsT EVal{} = Set.empty

eApp :: Id -> ETerm t v -> ETerm t v
eApp f (ECase t ps) = ECase t $ map (second $ eApp f) ps
eApp f (ELet v t' t) = ELet v t' $ eApp f t
eApp f t = EApp f t

aApp :: Prim v t => Alg t v -> ETerm t v -> TcM t v (ETerm t v)
aApp Id  t = pure t
aApp (Proj i _) (EPair ps)
  | length ps > 1 = pure $ ps !! i
aApp (Proj i j) t = pure $ eProj i j t
aApp (Inj i j) t = pure $ EInj i j t
aApp e p = eApp <$> getDefnId e <*> pure p

eProj :: Int -> Int -> ETerm t v -> ETerm t v
eProj i _ (EPair ps) = ps !! i
eProj i j e          = EProj i j e

eLet :: Id -> ETerm t v -> ETerm t v -> ETerm t v
eLet v0 (EVar v1) t1 = sbst v0 (EVar v1) t1
eLet v t1 t2 = ELet v t1 t2

eCase :: ETerm t v -> [(Id, ETerm t v)] -> ETerm t v
eCase (ELet v t1 t2) ls = eLet v t1 $ eCase t2 ls
eCase (ECase t ps) ls = eCase t $! map go ps
  where
    go (v, e) = (v, eCase e ls)
eCase (EInj i _ t) ls = eLet v1 t t1
  where
    (v1, t1) = ls !! i
eCase t ls = ECase t ls

data EFun t v
  = EAbs !(Maybe Id) !(EMonad t v)
  deriving (Show, Eq)

type ChannelId = Int

data EMonad t v
  = ERet !(ETerm t v)
  | EBnd !(EMonad t v) !(EFun t v)
  | ERun !(ETerm t v)
  | ESnd !ChannelId !(ETerm t v)
  | ERcv !ChannelId
  | ECh  ![ChannelId] !(ETerm t v) ![EFun t v]
  | EBrn !ChannelId ![EMonad t v]
  deriving (Show, Eq)

eRun :: (ETerm t v) -> EMonad t v
eRun t@EVar{} = ERet t
eRun t = ERun t

fvsM :: EMonad t v -> Set Id
fvsM (ERet t) = fvsT t
fvsM (ERun t) = fvsT t
fvsM (EBnd m1 f2) = fvsM m1 `Set.union` fvsF f2
fvsM (ESnd _ t) = fvsT t
fvsM (ECh _ t fs) = Set.unions $ fvsT t : map fvsF fs
fvsM (EBrn _ ms) = Set.unions $ map fvsM ms
fvsM ERcv{} = Set.empty

fvsF :: EFun t v -> Set Id
fvsF (EAbs i m2) = fvsM m2 Set.\\ maybe Set.empty Set.singleton i

ecomp :: EFun t v -> EFun t v -> EFun t v
ecomp (EAbs x m) f = EAbs x (ebnd m f)

retM :: EMonad t v -> EMonad t v -> EMonad t v
retM ERet{} m = m
retM (EBnd m1 (EAbs x m2)) m = EBnd m1 (EAbs x $ retM m2 m)
retM (ECh sf e fs) m = ECh sf e $ map (`ecomp` EAbs Nothing m) fs
retM (EBrn sf ms) m = EBrn sf $ map (`retM` m) ms
retM m m1 = EBnd m $ EAbs Nothing m1

ebnd :: EMonad t v -> EFun t v -> EMonad t v
-- ebnd m@(ERet EApp{}) f = EBnd m f
ebnd   (ERet t     ) f = app f t
ebnd m (EAbs x (ERet (EVar y)))
  | x == Just y = m
ebnd m (EAbs Nothing  m1@ERet{}) = retM m m1
ebnd m (EAbs (Just i) m1@ERet{})
  | i `Set.notMember` fvsM m1 = retM m m1
ebnd m (EAbs (Just i) m1)
  | i `Set.notMember` fvsM m1 = ebnd m $ EAbs Nothing m1
ebnd (EBnd m f1)  f2   = ebnd m (f1 `ecomp` f2)
ebnd m               f = EBnd m f

ebndr :: EMonad t v -> EFun t v -> EMonad t v
ebndr   (ERet t     ) f = app f t
ebndr m (EAbs x (ERet (EVar y)))
  | x == Just y = m
ebndr m (EAbs Nothing  m1@ERet{}) = retM m m1
ebndr m (EAbs (Just i) m1@ERet{})
  | i `Set.notMember` fvsM m1 = retM m m1
ebndr m (EAbs (Just i) m1)
  | i `Set.notMember` fvsM m1 = ebndr m $ EAbs Nothing m1
ebndr (EBnd m f1)  f2   = ebndr m (f1 `ecompr` f2)
ebndr (ECh cs e ts)  f = ECh cs e $ map (`ecompr` f) ts
ebndr (EBrn c ts)  f = EBrn c $ map (`ebndr` f) ts
ebndr m f = EBnd m f

ecompr :: EFun t v -> EFun t v -> EFun t v
ecompr (EAbs x m1) f = EAbs x (ebndr m1 f)

app :: EFun t v -> ETerm t v -> EMonad t v
app (EAbs i m) v = go m
  where
    go (ERet v') = ERet $! msbst i v v'
    go (ERun v') = eRun $! msbst i v v'
    go (EBnd m1 f) = ebnd (go m1) (substF f)
    go (ESnd c v') = ESnd c $! (msbst i v) v'
    go m1@ERcv{} = m1
    go (ECh c v' fs) = ECh c (msbst i v v') $! map substF fs
    go (EBrn c ms) = EBrn c $! map go ms

    substF f@(EAbs j m1)
      | i == j = f
      | otherwise = EAbs j $! go m1

msbst :: Maybe Id -> ETerm t v -> ETerm t v -> ETerm t v
msbst Nothing  _ v' = v'
msbst (Just i) v v' = sbst i v v'

sbst :: Id -> ETerm t v -> ETerm t v -> ETerm t v
sbst i v v'@(EVar j)
 | i == j = v
 | otherwise = v'
sbst _ _ x@EVal{} = x
sbst _ _ x@EUnit  = x
sbst i v (EPair es) = EPair $! map (sbst i v) es
sbst i v (EInj j k e) = EInj j k $! (sbst i v) e
sbst i v (EProj j k e) = eProj j k $! (sbst i v) e
sbst i v (ECase t alts) = eCase (sbst i v t) $! map (second $ sbst i v) alts
sbst i v (EApp f x) = eApp f (sbst i v x)
sbst i v (ELet v' t1 t2)
  | i == v' = ELet v' (sbst i v t1) t2
  | otherwise = ELet v' (sbst i v t1) (sbst i v t2)

data EProg t v
  = EProg { getHs :: Map Id (Id, ETerm t v)
          , getEnv :: Map Id (ParProg t v)
          }

type ParProg t v = Map RoleId (EFun t v)

hAbs :: TcM t v (EFun t v) -> ETerm t v -> TcM t v (EMonad t v)
hAbs f t = (`app` t) <$!> f

mRet :: ETerm t v -> TcM t v (EMonad t v)
mRet t = ERet <$> pure t

mRun :: ETerm t v -> TcM t v (EMonad t v)
mRun t = eRun <$> pure t

eAbs :: TcM t v Int -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EFun t v)
eAbs var f = var >>= \ x -> EAbs (Just $ mkV x) <$!> f (EVar $ mkV x)


mkV :: Int -> Id
mkV i = mkId i $ "v" ++ show i

mBnd :: TcM t v Int -> TcM t v (EMonad t v) -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EMonad t v)
mBnd var m f = ebnd <$> m <*> eAbs var f

mBndR :: TcM t v Int -> TcM t v (EMonad t v) -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EMonad t v)
mBndR var m f = ebndr <$> m <*> eAbs var f

mPair :: TcM t v Int -> [TcM t v (EMonad t v)] -> TcM t v (EMonad t v)
mPair var = go []
  where
    go [e] [] = mRet e
    go es  [] = mRet $! EPair $! reverse es
    go es (m:ms) = mBnd var m $ \x -> go (x : es) ms

mSplit :: TcM t v Int -> [ETerm t v -> TcM t v (EMonad t v)] -> TcM t v (EFun t v)
mSplit var fs = eAbs sameVar $ \x -> mPair var $! map ($! x) fs

--mSplitA :: TcM t v Int -> [EAlt t v] -> TcM t v (EFun t v)
--mSplitA var fs = eAbs sameVar $ \x -> mPairA var $! map ($! x) (appA fs)
--  where
--    appA (Leaf f) x = Leaf (hAbs f x)
--    appA (ENode ts) x = ENode $ map (`appA` x) ts

eDiscard :: TcM t v (EMonad t v) -> TcM t v (EFun t v)
eDiscard m = EAbs Nothing <$!> m

mThen :: TcM t v (EMonad t v) -> TcM t v (EMonad t v) -> TcM t v (EMonad t v)
mThen m1 m2 = ebnd <$> m1 <*> eDiscard m2

mSnd :: (Ord t, Pretty t) => RoleId -> RoleId -> Type t -> ETerm t v -> TcM t v (EMonad t v)
mSnd r1 r2 ty tm = ESnd <$> (getChannelId (r1, r2, ty)) <*> pure tm

mRcv :: (Ord t, Pretty t) => RoleId -> RoleId -> Type t -> TcM t v (EMonad t v)
mRcv r2 r1 ty = ERcv <$> getChannelId (r1, r2, ty)

mCh :: (Ord t, Pretty t) => RoleId -> ETerm t v -> [RoleId] -> [ETerm t v -> TcM t v (EMonad t v)] -> TcM t v (EMonad t v)
mCh r1 t rs fs = ECh <$> mapM getChannelId chs <*> pure t <*> mapM (eAbs sameVar) fs
  where
    chs = zip3 (repeat r1) rs $ repeat (TSum (map (const TUnit) fs) Nothing)

mBrn :: (Ord t, Pretty t) => RoleId -> RoleId -> [TcM t v (EMonad t v)] -> TcM t v (EMonad t v)
mBrn r2 r1 ms = EBrn <$> getChannelId (r1, r2, unit) <*> sequence ms
  where
    unit = TSum (map (const TUnit) ms) Nothing

mComp :: TcM t v (EFun t v) -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EFun t v)
mComp m1 f1 = liftM2 ecomp m1 (eAbs newVar f1)

--mCompr :: TcM t v (EFun t v) -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EFun t v)
--mCompr m1 f1 = liftM2 ecompr m1 (eAbs newVar f1)

fId :: TcM t v (EFun t v)
fId = eAbs sameVar $ \x -> mRet x

--------------------------------------------------------------------------------
-- Translation

-- Pre: no alternative or choice
cmsg :: Prim v t => RoleId -> RoleId -> AType t -> TcM t v (EFun t v)
cmsg r r2 (TyAnn ty r1)
  | r == r1 && r /= r2 = eAbs sameVar $ \ x -> mSnd r r2 ty x `mThen` mRet x
  | r /= r1 && r == r2 = eDiscard $ mRcv r r1 ty
  | otherwise       = fId
cmsg r r2 (TyPrd rs)
  | r == r2    = prd newVar
  | otherwise = eAbs newVar $ \x -> hAbs (prd sameVar) x `mThen` mRet x
  where
    prd var = mSplit var $!
              zipWith (\i r3 -> hAbs $
                        mComp (eAbs sameVar $ \x -> project i x >>= mRet)
                              (hAbs $ cmsg r r2 r3)
                      ) idxs rs

    project i x
      | size <= 1 = pure x
      | otherwise = aApp (Proj i size) x

    idxs = scanl' (+) 0 $ map containsR rs
    size = last idxs
    containsR r'
      | r `Set.member` typeRoles r' = 1
      | otherwise                   = 0
cmsg r r2 (TyBrn i j r1)
  | r == r2    = mComp next $ \ x -> mRet $ EInj i j x
  | otherwise = next
  where
    next = cmsg r r2 r1
cmsg _ _ TyAlt {} = fail "Error! Cannot generate message from alternative \
                         \to role. Choices must be resolved earlier."
cmsg _ _ TyApp {} = fail "Error! Cannot generate message from functor \
                         \to role. Choices must be resolved earlier."
cmsg _ _ TyMeta{} = fail "Error! Cannot generate message from metavariable \
                          \to role. Choices must be resolved earlier."

data MAlt t = ELeaf t | ENode [MAlt t]

type EAlt t v = MAlt (EFun t v)

instance Pretty t => Pretty (MAlt t) where
  pretty (ELeaf f) = pretty "leaf " <+> pretty f
  pretty (ENode fs) = pretty "alts " <+> pretty fs


genAlt :: Prim v t => RoleId -> ATerm t v -> AType t -> TcM t v (EAlt t v)
genAlt r e (TyAlt as) = do

  (_, gss) <- trace (render as ++ "\n" ++ render e ++ "\n" ++ render r ++ "\n\n") $ unzip <$!> mapM (`protoInfer` e) as
  let (_ , as') = unzip $! filter ((r `Set.member`) . gRoles . fst) $! zip gss as
  eNode <$!> mapM (genAlt r e) as'
  where
    eNode [t] = t
    eNode es = ENode es
genAlt r e r1         = ELeaf <$!> gen r e r1

seqAltsF :: Prim v t => EFun t v -> EAlt t v -> EFun t v
seqAltsF mf1 (ELeaf mf2) = ecomp mf1 mf2
seqAltsF (EAbs x m1) e = EAbs x $! seqAlts m1 e

seqAlts :: Prim v t => EMonad t v -> EAlt t v -> EMonad t v
seqAlts m1 (ELeaf mf2)  = ebnd m1 mf2
seqAlts m1 (ENode []) = m1
seqAlts m1 n@(ENode alts) = go m1
  where
    go (ECh  c v as) = ECh c v $! zipWith seqAltsF as alts
    go (EBrn c   ms) = EBrn c $! zipWith seqAlts ms alts
    go (EBnd m2 (EAbs y m3)) = ebnd m2 $! EAbs y $! go m3
    go t@ERet{} = error $ "Panic! ill-formed sequencing of computations 'seqAlts ret'" ++ render t ++ "\n" ++ render n
    go t@ERun{} = error $ "Panic! ill-formed sequencing of computations 'seqAlts run'" ++ render t ++ "\n" ++ render n
    go ESnd{} = error "Panic! ill-formed sequencing of computations 'seqAlts send'"
    go ERcv{} = error "Panic! ill-formed sequencing of computations 'seqAlts receive'"

doChoice :: (Ord t, Pretty t)
         => RoleId
         -> RoleId
         -> [RoleId]
         -> [TcM t v (EFun t v)]
         -> TcM t v (EFun t v)
doChoice r r1 rs fs =
    if r1 == r
    -- I do the choice
    then eAbs sameVar $ \ x -> mCh r x rs $ map hAbs fs
    else if r `Set.member` Set.fromList rs
         then eAbs sameVar $ \ x -> mBrn r r1 $ map (`hAbs` x) fs
         else fId

dupBranches :: Prim v1 t
            => RoleId
            -> AType t
            -> [ATerm t v1]
            -> TcM t v1 (EFun t v1)
dupBranches r a ps = do
  (rs1, _) <- unzip <$!> mapM (inferGTy a) ps
  let (rs, ps1) = unzip $! ps' rs1
      ts = map (\ts1 -> gen r ts1 a) ps1
  i <- needBranch rs
  let t1 = take i ts
      ts2 = drop i ts
  seqChoices rs t1 ts2
  where
    seqChoices rs t1 ts2 = eAbs newVar $ \x -> do
      let ms1 = map (`hAbs` x) t1
      let ms2 = map (`hAbs` x) ts2
      go x [] ms1 ms2
      where
        go vi es  [] [] = mRet $!
                          pair $!
                          map snd $!
                          filter ((r `Set.member`) . typeRoles . fst) $
                          zip rs $
                          reverse es
          where
            pair []  = vi
            pair [e] = e
            pair es' = EPair $! es'
        go  vi vs  [] (e:es) = mBndR newVar e $ \x -> go vi (x : vs) [] es
        go  vi vs (e:es) ts = mBnd newVar e $ \x -> go vi (x : vs) es ts
    ps' rs
      = zip rs ps
      -- -- if we are projecting the input role, we need to cover all cases
      -- | r `Set.member` typeRoles a = zip rs ps
      -- -- if r is in rs, but not in ps, then 'r' must be in 'a', covered by previous case
      -- | otherwise = filter ((r `Set.member`) . termRoles . snd) $ zip rs ps

gen :: Prim v t => RoleId -> ATerm t v -> AType t -> TcM t v (EFun t v)
gen r p (TyAnn (TApp f a) r1) =
  appPoly f a >>= \b -> gen r p (TyAnn b r1)

-- gen r e r1
--   | r `Set.notMember` (termRoles e `Set.union` typeRoles r1)
--   = fId

gen r p a
  | Just (r1, as) <- tryChoice a p = do
      (_, g) <- inferGTy a p
      doChoice r r1 (getChRoles g) $! map (gen r p) as
  where
    getChRoles (Choice _ rs _) = rs
    getChRoles _ = error "Panic! should be a choice at EMonad.gen"
--  where
--    !rs = Set.toList $! r `Set.delete` (typeRoles a `Set.union` termRoles p)

gen r (AnnAlg e r2) r1
  | r == r2    = cmsg r r2 r1 `mComp` \ x -> aApp e x >>= mRun
  | otherwise = cmsg r r2 r1

gen r e@(AnnComp es) r1 = keepCtx r r1 e $! go $! reverse es
  where
    go []    = fId
    go (h:t) = do
      a <- gen r h r1
      (r3, _) <- inferGTy r1 h
      b <- genAlt r (AnnComp $ reverse t) r3
      pure $! seqAltsF a b
--        where
--          genComp rr
--            | r `Set.notMember` (Set.unions $ typeRoles rr : map termRoles t)
--            = ELeaf <$> fId
--          genComp (TyAlt rs@(r3:_))
--            | all (== r3) rs = genComp r3
--            | otherwise    = ENode <$!> mapM genComp rs
--          genComp r3       = ELeaf <$!> genN r3
--
--          genN (TyAnn (TApp f a) r3) =
--            appPoly f a >>= \b -> genN (TyAnn b r3)
--
--          genN r3
--            | r `Set.notMember` (Set.unions $ typeRoles r3 : map termRoles t)
--            = fId
--
--          genN a
--            | Just (rc, as) <- tryChoice a (AnnComp $ reverse t)
--            = doChoice r rc rs $! map genN as
--            where
--              !rs = Set.toList $! r `Set.delete` (Set.unions $ typeRoles a : map termRoles t)
--          genN a = go t a

gen r (AnnPrj i j) (TyAnn _ r1)
  | r == r1 = eAbs sameVar $ \x -> aApp (Proj i j) x >>= mRet
gen r (AnnPrj i _) (TyPrd rs)
  | size > 1 = eAbs sameVar $ \x -> aApp (Proj n size) x >>= mRet
  where
    n = idxs !! i
    idxs = scanl' (+) 0 $ map containsR rs
    size = last idxs
    containsR r'
      | r `Set.member` typeRoles r' = 1
      | otherwise                   = 0
gen _ (AnnPrj _ _) _ = eAbs sameVar $ \x -> mRet x

gen r (AnnSplit ps) r1 = dupBranches r r1 ps

gen r (AnnCase es) (TyBrn i _ a) = gen r (es !! i) a

gen _  _ (TyBrn i j _) = eAbs sameVar $ \x -> mRet $ EInj i j x
gen _ AnnInj{} _ = fId
gen _ AnnId _ = fId

gen _ AnnCase{} _ = fail "EMonad.gen: case expression reached a non-branch type"
gen _ AnnFmap{} _ = fail "EMonad.gen: functors not (yet) supported"


keepCtx :: Prim v t
        => RoleId
        -> AType t
        -> ATerm t v
        -> TcM t v (EFun t v)
        -> TcM t v (EFun t v)
keepCtx r r1 e m = do
  (r2, _) <- inferGTy r1 e -- Check the output roles
  if r `Set.member` typeRoles r2
    then m
    else eAbs newVar $ \x -> hAbs m x `mThen` mRet x

--------------------------------------------------------------------------------
-- Typing endpoint code: TODO


--------------------------------------------------------------------------------
-- Prettyprinting instances

instance IsCompound (ETerm t v) where
  isCompound EVar {} = False
  isCompound EUnit{} = False
  isCompound EVal {} = False
  isCompound EPair{} = True
  isCompound EInj {} = True
  isCompound ECase{} = True
  isCompound ELet {} = True
  isCompound EProj{} = True
  isCompound EApp {} = True

instance forall t v. Prim v t => Pretty (ETerm t v) where
  pretty (EVar i) = pretty i
  pretty EUnit    = parens emptyDoc
  pretty (EVal v) = pretty v
  pretty (EPair ts) = hsep $ hcat [pretty "Pair", pretty $ length ts] : map pprParens ts
  pretty (EInj i j t) = hsep [ hcat [pretty "Inj", pretty i, pretty "_", pretty j]
                             , pprParens t
                             ]
  pretty (ECase ts alts) = hang 2 $ vsep $
    hsep [ pretty "case", pretty ts, pretty "of" ]
    : zipWith (<+>) delim ((zipWith pprAlts [0..] alts) ++ [emptyDoc])
    where
      nalts = length alts
      delim = (pretty "{")
              : take (nalts - 1) (repeat $ pretty ";")
              ++ [pretty "}"]
      pprAlts i (v, t) = hsep [ pretty (EInj i nalts (EVar v) :: ETerm t v)
                              , pretty "->"
                              , pretty t
                              ]

  pretty (ELet v t1 t2) = align $ vsep [ hsep [ pretty "let", pretty v, pretty "=", pretty t1 ]
                                       , hsep [ pretty "in", pretty t2 ]
                                       ]
  pretty (EProj i j t) = hsep [ hcat [pretty "proj", pretty i, pretty "_", pretty j]
                             , pprParens t
                             ]
  pretty (EApp e t) = hsep [hcat [ pretty e], pprParens t]

instance Prim v t => Pretty (EFun t v) where
  pretty (EAbs i m) = nest 2 $ vsep [ hsep [ pretty "\\"
                                           , pprVar i
                                           , pretty "->"
                                           ]
                                    , pretty m
                                    ]
    where
      pprVar Nothing = pretty "_"
      pprVar (Just v) = pretty v

instance forall v t. Prim v t => Pretty (EMonad t v) where
  pretty (ERet t)    = hsep [pretty "return", pprParens t]
  pretty blck@EBnd{} = hsep [ pretty "do"
                            , align $!
                              vsep $!
                              case go blck of
                                [] -> error "Panic! Impossible empty monadic action"
                                [x] -> [hsep [pretty "{", x, pretty "}"]]
                                (h:t@(_:_)) -> hsep [pretty "{", h]
                                        : ((map (pretty ";" <+>) t)
                                        ++ [pretty "}"])
                            ]
    where
      go (EBnd (ERet t) (EAbs (Just v1) m2))
        = hsep [ pretty "let"
               , pretty v1
               , pretty "="
               , pretty t
               ] : go m2
      go (EBnd m1 (EAbs Nothing m2))
        = hsep [pretty m1] : go m2
      go (EBnd m1 (EAbs (Just v1) m2))
        = hsep [ pretty v1
               , pretty "<-"
               , pretty m1] : go m2
      go m
        = [pretty m]
  pretty (ERun t)  = hsep [pretty "evaluate", parens $! hsep [pretty "force", pprParens t]]
  pretty (ESnd sf t) = hsep [pretty "writeChan", hcat [pretty "ch",pretty sf], pprParens t]
  pretty (ERcv sf)   = hsep [pretty "readChan", hcat [pretty "ch",pretty sf]]
  pretty (ECh c t a) = hang 2 $! pprChoice
    where
      pprChoice =
        vsep [ hsep [ pretty "case", pretty t, pretty "of" ]
             , encloseSep
               (pretty "{ ")
               (pretty " }")
               (pretty "; ")
               $! zipWith prettyCaseAlt [0..] a
             ]
      prettyCaseAlt i (EAbs v m) =
        hang 2 $ vsep
        [ hsep [ toHs (Inj i (length a) :: Alg t v)
               , maybe (pretty "_") pretty v
               , pretty "->"
               ]
        , pretty (sendTag i c m)
        ]
      sendTag _ [] k = k
      sendTag i (cc : cs) k = ESnd cc (EInj i (length a) EUnit) `ebnd` EAbs Nothing (sendTag i cs k)
  pretty (EBrn r a) = hang 2 $! pprBrn
    where
      pprBrn =
        hang 2 $
        vsep [ hsep [pretty "readChan", hcat [pretty "ch", pretty r], pretty ">>="
                    , hcat [pretty "\\ vch", pretty r, pretty " -> "] ]
             , hsep [ pretty "case", hcat [pretty "vch", pretty r], pretty "of" ]
             , encloseSep
               (pretty "{ ")
               (pretty " }")
               (pretty "; ")
               $! zipWith prettyCaseAlt [0..] a
             ]
      prettyCaseAlt i m =
        hang 2 $ vsep
        [ hsep [ toHs (Inj i (length a) :: Alg t v)
               , pretty "_"
               , pretty "->"
               ]
        , pretty m
        ]

renderPCode :: Prim v t => FilePath -> FilePath -> FilePath -> EProg t v -> String
renderPCode prel atoms fp pprog
  = renderString
  $! layoutSmart defaultLayoutOptions
  $! vsep
  $! (pprHeader ++)
  $! (map pprHs (Map.toList defs) ++)
  $! map pprPDefns
  $! Map.toList pd
  where
    pd = getEnv pprog
    defs = getHs pprog
    pprHeader =
      [ pretty "{-# OPTIONS_GHC -threaded #-}"
      , hsep [pretty "module", pretty $ toUpper (head fp) : tail fp, pretty "where" ]
      , line
      , pretty "import Control.Concurrent"
      , pretty "import Control.Exception"
      , pretty "import Control.DeepSeq"
      , pretty "import" <+> pretty prel
      , pretty "import" <+> pretty atoms
      , line
      , line
      ]
    pprHs (i, (v, d)) = hsep [pretty i, pretty v, pretty "=", pretty d, line ]
    pprPDefns (i, p)
      = vsep [ hsep [pretty "--", pretty i ]
             , hang 2 $
               vsep [ hsep [pretty i, pretty "inp ="]
                    , pprInit p
                    , hang 2 $
                      vsep $ pretty "where" : map pprCRole (Map.toList p)
                    ]
             , line
             ]
      where
        pprCRole (r, f@(EAbs v m)) = nest 2 $ vsep
                                     [ hsep [ hcat [pretty r]
                                            , hsep (prettyChans f)
                                            , pretty v
                                            , pretty "="
                                            ]
                                     , pretty m
                                     ]

renderPrelude :: String -> String
renderPrelude prf = renderString $ layoutSmart defaultLayoutOptions $ vsep prel
  where
    prel =
      [ pretty "{-# LANGUAGE DeriveGeneric #-}"
      , hsep [ pretty "module", pretty  prf, pretty "where" ]
      , line
      , pretty "import Control.DeepSeq"
      , pretty "import GHC.Generics (Generic, Generic1)"
      , line
      , vsep $ map mkPair [0..10]
      , vsep $ map mkSum [0..10]
      ]

mkPair :: Int -> Doc ann
mkPair i = vsep [ nest 4 $ vsep
                  [ hsep [ pretty "data", hcat [pretty "Pair", pretty i], hsep $ map pretty vs ]
                  , hsep [ hcat [pretty "= Pair", pretty i], hsep $ map ((pretty "!" <>) . pretty) vs ]
                  , pretty "deriving Generic"
                  ]
                , line
                , pretty "instance" <+> parens (hsep (punctuate (pretty ",") (map ((pretty "NFData" <+>) . pretty) vs)))
                  <+> pretty "=> NFData" <+> parens (hsep $ hcat [pretty "Pair", pretty i] : map pretty vs)
                , line
                , mkProjs i
                , line
                ]
  where
    vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]

mkProjs :: Int -> Doc ann
mkProjs i = vsep $ map mkProj [0..i-1]
  where
    mkProj j =
      hsep [ hcat [ pretty "proj", pretty j, pretty "_", pretty i ]
           , parens $ (pretty "Pair" <> pretty i) <+> hsep (map pretty vs)
           , pretty "="
           , pretty $ vs !! j
           ]
    vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]

mkSum :: Int -> Doc ann
mkSum i = vsep [ nest 4 $ vsep
                 $ hsep [ pretty "data", hcat [pretty "Sum", pretty i], hsep $ map pretty vs ]
                 : pprInjs ++ [pretty "deriving Generic"]
               , line
               , pretty "instance" <+> parens (hsep (punctuate (pretty ",") (map ((pretty "NFData" <+>) . pretty) vs)))
                 <+> pretty "=> NFData" <+> parens (hsep $ hcat [pretty "Sum", pretty i] : map pretty vs)
               , line
               ]
  where
    vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]
    pprInjs =
      case mkInjs i of
        [] -> []
        (h : t) -> (pretty "=" <+> h) : map (pretty "|" <+>) t

mkInjs :: Int -> [Doc ann]
mkInjs i = map mkInj [0..i-1]
  where
    mkInj j =
      hsep [ hcat [ pretty "Inj", pretty j, pretty "_", pretty i ]
           , hcat [ pretty "!", pretty $ vs !! j ]
           ]
    vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]

prettyChans :: EFun t v -> [Doc ann]
prettyChans = map ((pretty "ch" <>) . pretty) . Set.toList . getChans

pprInit :: ParProg t v -> Doc ann
pprInit p = hsep [ pretty "do"
                 , align $ vsep $ (hsep [pretty "{", pprNewCh ch])
                   : (map (pretty "; "<>)
                      ( map pprNewCh chs
                      ++ map pprCalls (Map.toList $ Map.delete (Rol 0) p)
                      ++ [hsep $ pretty "r0" : prettyChans (p Map.! Rol 0) ++ [pretty "inp" ]]
                      )) ++ [pretty "}"]
                 ]
  where
    (ch : chs) = Set.toList $ getPChans p
    pprCh = (pretty "ch" <>) . pretty
    pprNewCh c =  hsep [pprCh c, pretty "<- newChan"]
    pprCalls (r, c) = hsep $ pretty "_ <- forkIO $" : pretty r : map pprCh (Set.toList $ getChans c) ++ [pretty "()"]

getPChans :: ParProg t v -> Set Int
getPChans = Set.unions . map getChans . Map.elems

getChans :: EFun t v -> Set Int
getChans (EAbs _ m) = go m
  where
    go (EBnd m1 f) = Set.union (go m1) (getChans f)
    go (ESnd c _) = Set.singleton c
    go (ERcv c) = Set.singleton c
    go (EBrn c ms1) = Set.unions $ Set.singleton c : map go ms1
    go (ECh cs _ fs1 ) = Set.unions $ Set.fromList cs : map getChans fs1
    go _ = Set.empty

toHsParens :: (Pretty a, Pretty t) => Alg t a -> Doc ann
toHsParens x
  | isCompound x = parens (toHs x)
  | otherwise    = toHs x

toHs :: (Pretty a, Pretty t) => Alg t a -> Doc ann
toHs (Var  v  ) = pretty v
toHs (Val  v)   = pretty v
toHs (Const c)  = hsep [pretty "const", pprParens c]
toHs Unit       = pretty "()"
toHs (Comp es)
  = group $! encloseSep emptyDoc emptyDoc (pretty " . ") $! fmap toHs es
toHs Id         = pretty "id"
toHs (Proj i j)   = hcat [pretty "proj", pretty i, pretty "_", pretty j]
toHs (Split es)
  = pretty "split" <> pretty (length es) <+>
         (group $! cat $! fmap toHsParens es)
toHs (Inj i j)    = hcat [pretty "Inj", pretty i, pretty "_", pretty j]
toHs (Case es)
  = pretty "join" <> pretty (length es) <+>
  (group $! cat $! fmap toHsParens es)
toHs (In f)     = hcat [pretty "<IN>", pretty f]
toHs (Out f)    = hcat [pretty "<OUT>", pretty f]
toHs _ = error "Panic! Unimplemented"

convertToHs :: forall v t.
              Prim v t
            => Id
            -> Alg t v
            -> TcM t v (Id, ETerm t v)
convertToHs _ (Rec dfn pf e1 e2) = do
  v <- mkV <$> newVar
  spl <- toETerm e2 (EVar v)
  mpr <- appPolyF pf (Var dfn)
  ar <- toETerm mpr spl
  tr <- toETerm e1 ar
  pure (v, tr)
convertToHs _defn x = do
  v <- mkV <$> newVar
  t <- toETerm x (EVar v)
  return (v, t)

toETerm :: Prim v t
        => Alg t v
        -> ETerm t v
        -> TcM t v (ETerm t v)
toETerm (Var  w)  t = pure (eApp w t)
toETerm (Val  _)  _ = error "convertToHs: Cannot apply value to variable"
toETerm Unit      _ = error "convertToHs: Cannot apply value to variable"
toETerm (Const c) _ = pure $ go c -- toETerm c >>= \t -> pure $ hsep [pretty "const", t]
  where
    go (Var w) = EVar w
    go (Val v) = EVal v
    go Unit    = EUnit
    go _       = error "convertToHs: Not a value"
toETerm (Comp es) t = rev es t
  where
    rev []     tm = pure tm
    rev (h:ts) tm = rev ts tm >>= \ hs -> toETerm h hs
toETerm Id       t = pure t
toETerm (Proj i j) t =
  case t of
    EPair ts -> pure (ts !! i)
    _        -> pure $ eProj i j t
toETerm (Split es) t
  = EPair <$> mapM (`toETerm` t) es
toETerm (Inj i j) t  = pure $ EInj i j t
toETerm (Case es) (EInj i _ t) = toETerm (es !! i) t
toETerm (Case es) t = do
  vs <- mapM (const newVar) es
  (eCase t . zipWith (\v tm -> (mkV v, tm)) vs) <$> zipWithM toETerm es (map (EVar . mkV) vs)
toETerm (Fmap pf g) t = appPolyF pf g >>= \ e -> toETerm e t
toETerm (Rec dn _pf _e1 _e2) t
  = pure $ EApp dn t
toETerm (In  _) t = newVar >>= \i -> pure (eApp (mkId i "rin") t) -- FIXME: in/out
toETerm (Out _) t = newVar >>= \i -> pure (eApp (mkId i "rout") t) -- FIXME: in/out

-- renderAtoms :: TyEnv t ->
-- renderAtoms = vsgo . Map.toList
--   where
--     go ()
