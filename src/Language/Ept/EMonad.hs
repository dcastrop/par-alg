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
  ) where

import Control.Monad.RWS.Strict
import Data.Char ( toUpper )
import Data.Map ( Map )
import Data.Set ( Set )
import Data.List ( scanl' )
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.SessionTypes.Common ( Role(..) )
import Language.Common.Id
import Language.Alg.Syntax
import Language.Alg.Typecheck
import Language.Alg.Internal.TcM
import Language.Alg.Internal.Ppr
import Language.Par.Role
import Language.Par.Term
import Language.Par.Type
import Language.Par.Prog
-- import Language.SessionTypes.Common hiding (Role)

generate :: Prim v t => TcSt t v -> AProg t v -> IO (Int, Map Id (ParProg t v))
generate tcst p = return (nextVar st, a)
  where
    (a, st, _w) = runRWS (genProg p) () tcst

genProg :: Prim v t => AProg t v -> TcM t v (Map Id (ParProg t v))
genProg defs = do
  par <- Map.fromList <$!> mapM genDef defs
  hsDefs <- (defnsR <$> get) >>= Map.traverseWithKey convertToHs
  pure par
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
        rs = Set.toList $! typeRoles aty `Set.union` termRoles p

close :: RoleId -> AType t -> TcM t v (EAlt t v)
close r (TyAlt ts) = ENode <$> mapM (close r) ts
close r (TyBrn i j a)
  | r `Set.member` typeRoles a = ELeaf <$> eAbs sameVar (\x -> mRet (EInj i j x))
close _ _ = ELeaf <$> fId


data ETerm t v
  = EVar !Int
  | EVal !v
  | EUnit
  | EPair ![ETerm t v]
  | EProj !Int !Int !(ETerm t v)
  | EInj !Int !Int !(ETerm t v)
  | EApp !Id !(ETerm t v)
  deriving (Show, Eq)

eApp :: Prim v t => Alg t v -> ETerm t v -> TcM t v (ETerm t v)
eApp Id  t = pure t
eApp (Proj i _) (EPair ps)
  | length ps > 1 = pure $ ps !! i
eApp (Proj i j) t = pure $ EProj i j t
eApp (Inj i j) t = pure $ EInj i j t
eApp e p = EApp <$> getDefnId e <*> pure p


data EFun t v
  = EAbs !(Maybe Int) !(EMonad t v)
  deriving (Show, Eq)

type ChannelId = Int

data EMonad t v
  = ERet !(ETerm t v)
  | EBnd !(EMonad t v) !(EFun t v)
  | ESnd !ChannelId !(ETerm t v)
  | ERcv !ChannelId
  | ECh  ![ChannelId] !(ETerm t v) ![EFun t v]
  | EBrn !ChannelId ![EMonad t v]
  deriving (Show, Eq)

fvsT :: ETerm t v -> Set Int
fvsT (EVar i) = Set.singleton i
fvsT (EPair ts) = Set.unions $ map fvsT ts
fvsT (EInj _ _ t) = fvsT t
fvsT (EApp _ t) = fvsT t
fvsT _ = Set.empty


fvsM :: EMonad t v -> Set Int
fvsM (ERet t) = fvsT t
fvsM (EBnd m1 f2) = fvsM m1 `Set.union` fvsF f2
fvsM (ESnd _ t) = fvsT t
fvsM (ECh _ t fs) = Set.unions $ fvsT t : map fvsF fs
fvsM (EBrn _ ms) = Set.unions $ map fvsM ms
fvsM ERcv{} = Set.empty

fvsF :: EFun t v -> Set Int
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
ebnd m@(ERet EApp{}) f = EBnd m f
ebnd   (ERet t     ) f = app f t
ebnd m (EAbs x (ERet (EVar y)))
  | x == Just y = m
ebnd m (EAbs Nothing  m1@ERet{}) = retM m m1
ebnd m (EAbs (Just i) m1@ERet{})
  | i `Set.notMember` fvsM m1 = retM m m1
ebnd m (EAbs (Just i) m1)
  | i `Set.notMember` fvsM m1 = EBnd m $ EAbs Nothing m1
ebnd (EBnd m f1)  f2   = EBnd m (f1 `ecomp` f2)
ebnd m               f = EBnd m f

app :: EFun t v -> ETerm t v -> EMonad t v
app (EAbs i m) v = go m
  where
    go (ERet v') = ERet $! sbst v'
    go (EBnd m1 f) = ebnd (go m1) (substF f)
    go (ESnd c v') = ESnd c $! sbst v'
    go m1@ERcv{} = m1
    go (ECh c v' fs) = ECh c (sbst v') $! map substF fs
    go (EBrn c ms) = EBrn c $! map go ms

    sbst v'@(EVar j)
     | i == Just j = v
     | otherwise = v'
    sbst x@EVal{} = x
    sbst x@EUnit  = x
    sbst (EPair es) = EPair $! map sbst es
    sbst (EInj j k e) = EInj j k $! sbst e
    sbst (EProj j k e) = EProj j k $! sbst e
    sbst (EApp f x) = EApp f (sbst x)

    substF f@(EAbs j m1)
      | i == j = f
      | otherwise = EAbs j $! go m1

data EProg t v
  = EptEnv { getEnv :: ParProg t v }

type ParProg t v = Map RoleId (EFun t v)

hAbs :: TcM t v (EFun t v) -> ETerm t v -> TcM t v (EMonad t v)
hAbs f t = (`app` t) <$!> f

mRet :: ETerm t v -> TcM t v (EMonad t v)
mRet t = ERet <$> pure t

eAbs :: TcM t v Int -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EFun t v)
eAbs var f = var >>= \ x -> EAbs (Just x) <$!> f (EVar x)

mBnd :: TcM t v Int -> TcM t v (EMonad t v) -> (ETerm t v -> TcM t v (EMonad t v)) -> TcM t v (EMonad t v)
mBnd var m f = ebnd <$> m <*> eAbs var f

mPair :: TcM t v Int -> [TcM t v (EMonad t v)] -> TcM t v (EMonad t v)
mPair var = go []
  where
    go [e] [] = mRet e
    go es  [] = mRet $! EPair $! reverse es
    go es (m:ms) = mBnd var m $ \x -> go (x : es) ms

mSplit :: TcM t v Int -> [ETerm t v -> TcM t v (EMonad t v)] -> TcM t v (EFun t v)
mSplit var fs = eAbs sameVar $ \x -> mPair var $! map ($! x) fs

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
mComp m1 f1 = liftM2 ecomp m1 (eAbs sameVar f1)

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
      | otherwise = eApp (Proj i size) x

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

data EAlt t v = ELeaf (EFun t v) | ENode [EAlt t v]


genAlt :: Prim v t => RoleId -> ATerm t v -> AType t -> TcM t v (EAlt t v)
genAlt r e (TyAlt rs@(r1:_))
  | all (== r1) rs = genAlt r e r1
  | otherwise    = ENode <$!> mapM (genAlt r e) rs
genAlt r e r1         = ELeaf <$!> gen r e r1

seqAltsF :: EFun t v -> EAlt t v -> EFun t v
seqAltsF mf1 (ELeaf mf2) = ecomp mf1 mf2
seqAltsF (EAbs x m1) e = EAbs x $! seqAlts m1 e

seqAlts :: EMonad t v -> EAlt t v -> EMonad t v
seqAlts m1 (ELeaf mf2)  = EBnd m1 mf2
seqAlts m1 (ENode alts) = go m1
  where
    go (ECh  c v as) = ECh c v $! zipWith seqAltsF as alts
    go (EBrn c   ms) = EBrn c $! zipWith seqAlts ms alts
    go (EBnd m2 (EAbs y m3)) = EBnd m2 $! EAbs y $! go m3
    go ERet{} = error "Panic! ill-formed sequencing of computations 'seqAlts ret'"
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
    else eAbs sameVar $ \ x -> mBrn r r1 $ map (`hAbs` x) fs

gen :: Prim v t => RoleId -> ATerm t v -> AType t -> TcM t v (EFun t v)
gen r p (TyAnn (TApp f a) r1) =
  appPoly f a >>= \b -> gen r p (TyAnn b r1)

gen r e r1
  | r `Set.notMember` (termRoles e `Set.union` typeRoles r1)
  = fId

gen r p a
  | Just (r1, as) <- tryChoice a p
  = doChoice r r1 rs $! map (gen r p) as
  where !rs = Set.toList $! r `Set.delete` (typeRoles a `Set.union` termRoles p)

gen r (AnnAlg e r2) r1
  | r == r2    = cmsg r r2 r1 `mComp` \ x -> eApp e x >>= mRet
  | otherwise = cmsg r r2 r1

gen r e@(AnnComp es) r1 = keepCtx r r1 e $ go (reverse es) r1
  where
    go []    _ = fId
    go (h:t) r2 = do
      (r3, _) <- inferGTy r2 h
      seqAltsF <$!> gen r h r2
        <*> genComp r3
        where
          genComp (TyAlt rs@(r3:_))
            | all (== r1) rs = genComp r3
            | otherwise    = ENode <$!> mapM genComp rs
          genComp r3       = ELeaf <$!> genN r3

          genN (TyAnn (TApp f a) r3) =
            appPoly f a >>= \b -> genN (TyAnn b r3)

          genN r3
            | r `Set.notMember` (Set.unions $ typeRoles r3 : map termRoles t)
            = fId

          genN a
            | Just (rc, as) <- tryChoice a (AnnComp $ reverse t)
            = doChoice r rc rs $! map genN as
            where
              !rs = Set.toList $! r `Set.delete` (Set.unions $ typeRoles a : map termRoles t)
          genN a = go t a

gen r (AnnPrj i j) (TyAnn _ r1)
  | r == r1 = eAbs sameVar $ \x -> eApp (Proj i j) x >>= mRet
gen r (AnnPrj i _) (TyPrd rs)
  | size > 1 = eAbs sameVar $ \x -> eApp (Proj n size) x >>= mRet
  where
    n = idxs !! i
    idxs = scanl' (+) 0 $ map containsR rs
    size = last idxs
    containsR r'
      | r `Set.member` typeRoles r' = 1
      | otherwise                   = 0
gen _ (AnnPrj _ _) _ = eAbs sameVar $ \x -> mRet x

gen r (AnnSplit ps) r1 = do
  prd
  where
    prd = mSplit newVar $! map (\p -> hAbs $ gen r p r1) ps'
    ps'
      | r `Set.member` typeRoles r1 = ps
      | otherwise = filter ((r `Set.member`) . termRoles) ps

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
  isCompound EProj{} = True
  isCompound EApp {} = True

instance Prim v t => Pretty (ETerm t v) where
  pretty (EVar i) = hcat [pretty "v", pretty i]
  pretty EUnit    = parens emptyDoc
  pretty (EVal v) = pretty v
  pretty (EPair ts) = hsep $ hcat [pretty "Pair", pretty $ length ts] : map pprParens ts
  pretty (EInj i j t) = hsep [ hcat [pretty "Inj", pretty i, pretty "_", pretty j]
                             , pprParens t
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
      pprVar (Just v) = hcat [pretty "v", pretty v]

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
               , hcat [pretty "v", pretty v1]
               , pretty "="
               , pretty t
               ] : go m2
      go (EBnd m1 (EAbs Nothing m2))
        = hsep [pretty m1] : go m2
      go (EBnd m1 (EAbs (Just v1) m2))
        = hsep [ hcat [pretty "v", pretty v1]
               , pretty "<-"
               , pretty m1] : go m2
      go m
        = [pretty m]
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
               , maybe (pretty "_") ((pretty "v" <>) . pretty) v
               , pretty "->"
               ]
        , pretty (sendTag i c m)
        ]
      sendTag _ [] k = k
      sendTag i (cc : cs) k = ESnd cc (EInj i (length a) EUnit) `EBnd` EAbs Nothing (sendTag i cs k)
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

renderPCode :: Prim v t => FilePath -> Map Id (ParProg t v) -> String
renderPCode fp
  = renderString
  . layoutSmart defaultLayoutOptions
  . vsep
  . (pprHeader ++)
  . map pprPDefns
  . Map.toList
  where
    pprHeader =
      [ hsep [pretty "module", pretty $ toUpper (head fp) : tail fp, pretty "where" ]
      , line
      , pretty "import Control.Concurrent"
      , pretty "import AlgPrelude"
      , pretty "import " <> pretty ((toUpper (head fp) : tail fp) ++ "Atoms")
      , line
      , line
      ]
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
                                            , hcat [pretty "v", pretty v]
                                            , pretty "="
                                            ]
                                     , pretty m
                                     ]

-- mkPair :: Int -> Doc ann
-- mkPair i = vsep [ nest 4 $ vsep
--                   [ hsep [ pretty "data", hcat [pretty "Pair", pretty i], hsep $ map pretty vs ]
--                   , hsep [ hcat [pretty "= Pair", pretty i], hsep $ map pretty vs  ]
--                   ]
--                 , mkProjs i
--                 ]
--   where
--     vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]
--
-- mkProjs :: Int -> Doc ann
-- mkProjs i = vsep $ map mkProj [0..i-1]
--   where
--     mkProj j =
--       hsep [ hcat [ pretty "proj", pretty j, pretty "_", pretty i ]
--            , hsep $ map pretty vs
--            , pretty "="
--            , pretty $ vs !! j
--            ]
--     vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]
--
-- mkSum :: Int -> Doc ann
-- mkSum i = vsep [ nest 4 $ vsep
--                  $ hsep [ pretty "data", hcat [pretty "Sum", pretty i], hsep $ map pretty vs ]
--                  : pprInjs
--                 ]
--   where
--     vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]
--     pprInjs =
--       case mkInjs i of
--         [] -> []
--         (h : t) -> (pretty "=" <+> h) : map (pretty "|" <+>) t
--
-- mkInjs :: Int -> [Doc ann]
-- mkInjs i = map mkInj [0..i-1]
--   where
--     mkInj j =
--       hsep [ hcat [ pretty "Inj", pretty j, pretty "_", pretty i ]
--            , pretty $ vs !! j
--            ]
--     vs = take i $ [ [c] | c <- ['a'..'z']] ++ [ [c] ++ show n | (n :: Integer) <- [0..], c <- ['a'..'z']]

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
-- toHs (Fmap f g) = error "Panic! Functors should not occur here"
-- toHs (Rec f e1 e2)
--   = hsep [toHs "rec", brackets (toHs f), pprParens e1, pprParens e2]

convertToHsP :: Prim v t
             => Int
             -> Alg t v
             -> TcM t v (Doc ann)
convertToHsP f a
  | isCompound a = convertToHs f a >>= pure . parens
  | otherwise = convertToHs f a

convertToHs :: forall v t ann.
              Prim v t
            => Int
            -> Alg t v
            -> TcM t v (Doc ann)
convertToHs f a = do
  v <- newVar
  next (pretty "v" <> pretty v) a
  where
    next t = go
      where
        go (Var  w  ) = pure $ hsep [pretty w, t]
        go (Val  x)   = pure $ hsep [pretty x, t]
        go (Const c)  = pure $ toHs c -- go c >>= \t -> pure $ hsep [pretty "const", t]
        go Unit       = pure $ hsep [pretty "()", t]
        go (Comp es)  = rev $ reverse es
          where
            rev [] = pure t
            rev (h:ts) = rev ts >>= \ hs -> next (parens hs) h
        go Id         = pure t
        go (Proj i j) = pure $ hsep [hcat [pretty "proj", pretty i, pretty "_", pretty j], t]
        go (Split es)
          = mapM go es >>= \hss -> pure $ hsep $ (pretty "Pair" <> pretty (length es)) : map parens hss
        go (Inj i j)    = pure $ hsep [hcat [pretty "Inj", pretty i, pretty "_", pretty j], t]
        go (Case es) = mapM (const newVar) es
          >>= \ vss -> zipWithM mkAlt (zip [0..] vss) es  >>= \ alts ->
          pure $ caseT alts
          where
            caseT as =
              vsep [ hsep [ pretty "case", t, pretty "of" ]
                   , encloseSep
                     (pretty "{ ")
                     (pretty " }")
                     (pretty "; ")
                     as
                   ]
            mkAlt (i, v) e =
              next (pretty "v" <> pretty v) e >>=
              \he ->
                pure $
                hang 2 $ vsep
                [ hsep [ toHs (Inj i (length es) :: Alg t v)
                       , pretty "v" <> pretty v
                       , pretty "->"
                       ]
                , he
                ]
   --  go (In f)     = hcat [pretty "<IN>", pretty f]
   --  go (Out f)    = hcat [pretty "<OUT>", pretty f]
   --  go _ = error "Panic! Unimplemented"
        go (Fmap pf g) = appPolyF pf g >>= \ e -> go e
        go (Rec f e1 e2) = go e2 >>= \he2 -> appPolyF f (Var f) >>= \ap -> next he2 ap >>= \ hap ->
          next hap e1
  --   = hsep [go "rec", brackets (go f), pprParens e1, pprParens e2]
