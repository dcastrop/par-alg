{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wwarn#-}
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
import Data.Map ( Map )
import Data.List ( scanl' )
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import qualified Data.Map as Map
import qualified Data.Set as Set

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

generate :: Prim v t => TcSt t -> AProg t v -> IO (Int, Map Id (ParProg t v))
generate tcst p = return (nextVar st, a)
  where
    (a, st, _w) = runRWS (genProg p) () tcst

genProg :: Prim v t => AProg t v -> TcM t (Map Id (ParProg t v))
genProg = undefined

data ETerm t v
  = EVar !Int
  | EVal !v
  | EUnit
  | EPair ![ETerm t v]
  | EInj !Int !(ETerm t v)
  | EApp !(Alg t v) !(ETerm t v)
  deriving (Show, Eq)

data EFun t v
  = EAbs !(Maybe Int) !(EMonad t v)
  deriving (Show, Eq)

data EMonad t v
  = ERet !(ETerm t v)
  | EBnd !(EMonad t v) !(EFun t v)
  | ESnd !RoleId !(ETerm t v)
  | ERcv !RoleId
  | ECh  !(ETerm t v) ![RoleId] ![EFun t v]
  | EBrn !RoleId ![EMonad t v]
  deriving (Show, Eq)

ecomp :: EFun t v -> EFun t v -> EFun t v
ecomp (EAbs x m) f = EAbs x (ebnd m f)

ebnd :: EMonad t v -> EFun t v -> EMonad t v
ebnd m@(ERet (EApp Var{} _)) f = EBnd m f
ebnd m@(ERet (EApp Comp{} _)) f = EBnd m f
ebnd m@(ERet (EApp Split{} _)) f = EBnd m f
ebnd m@(ERet (EApp Case{} _)) f = EBnd m f
ebnd m@(ERet (EApp Fmap{} _)) f = EBnd m f
ebnd m@(ERet (EApp Rec{} _)) f = EBnd m f
ebnd   (ERet t     ) f = app f t
ebnd m (EAbs x (ERet (EVar y)))
  | x == Just y = m
ebnd (EBnd m f1)  f2   = EBnd m (f1 `ecomp` f2)
ebnd m               f = EBnd m f

app :: EFun t v -> ETerm t v -> EMonad t v
app (EAbs i m) v = go m
  where
    go (ERet v') = ERet $! sbst v'
    go (EBnd m1 f) = ebnd (go m1) (substF f)
    go (ESnd r v') = ESnd r $! sbst v'
    go m1@ERcv{} = m1
    go (ECh v' r fs) = ECh (sbst v') r $! map substF fs
    go (EBrn r ms) = EBrn r $! map go ms

    sbst v'@(EVar j)
     | i == Just j = v
     | otherwise = v'
    sbst x@EVal{} = x
    sbst x@EUnit  = x
    sbst (EPair es) = EPair $! map sbst es
    sbst (EInj j e) = EInj j $! sbst e
    sbst (EApp f x) = EApp f (sbst x)

    substF f@(EAbs j m1)
      | i == j = f
      | otherwise = EAbs j $! go m1

data EProg t v
  = EptEnv { getEnv :: ParProg t v }

type ParProg t v = Map RoleId (EFun t v)

hAbs :: TcM t (EFun t v) -> ETerm t v -> TcM t (EMonad t v)
hAbs f t = (`app` t) <$!> f

mRet :: ETerm t v -> TcM t (EMonad t v)
mRet t = ERet <$> pure t

eAbs :: (ETerm t v -> TcM t (EMonad t v)) -> TcM t (EFun t v)
eAbs f = newVar >>= \ x -> EAbs (Just x) <$!> f (EVar x)

mBnd :: TcM t (EMonad t v) -> (ETerm t v -> TcM t (EMonad t v)) -> TcM t (EMonad t v)
mBnd m f = ebnd <$> m <*> eAbs f

mPair :: [TcM t (EMonad t v)] -> TcM t (EMonad t v)
mPair = go []
  where
    go [e] [] = mRet e
    go es  [] = mRet $! EPair $! reverse es
    go es (m:ms) = mBnd m $ \x -> go (x : es) ms

mSplit :: [ETerm t v -> TcM t (EMonad t v)] -> TcM t (EFun t v)
mSplit fs = eAbs $ \x -> mPair $! map ($! x) fs

eDiscard :: TcM t (EMonad t v) -> TcM t (EFun t v)
eDiscard m = EAbs Nothing <$!> m

mThen :: TcM t (EMonad t v) -> TcM t (EMonad t v) -> TcM t (EMonad t v)
mThen m1 m2 = ebnd <$> m1 <*> eDiscard m2

mSnd :: RoleId -> ETerm t v -> TcM t (EMonad t v)
mSnd = (pure .) . ESnd

mRcv :: RoleId -> TcM t (EMonad t v)
mRcv = pure . ERcv

mCh :: ETerm t v -> [RoleId] -> [ETerm t v -> TcM t (EMonad t v)] -> TcM t (EMonad t v)
mCh t rs fs = ECh t rs <$> mapM eAbs fs

mBrn :: RoleId -> [TcM t (EMonad t v)] -> TcM t (EMonad t v)
mBrn r ms = EBrn r <$> sequence ms

mComp :: TcM t (EFun t v) -> (ETerm t v -> TcM t (EMonad t v)) -> TcM t (EFun t v)
mComp m1 f1 = liftM2 ecomp m1 (eAbs f1)

fId :: TcM t (EFun t v)
fId = eAbs $ \x -> mRet x

--------------------------------------------------------------------------------
-- Translation

-- Pre: no alternative or choice
cmsg :: RoleId -> RoleId -> AType t -> TcM t (EFun t v)
cmsg r r2 (TyAnn _ r1)
  | r == r1 && r /= r2 = eAbs $ \ x -> mSnd r2 x `mThen` mRet x
  | r /= r1 && r == r2 = eDiscard $ mRcv r1
  | otherwise       = fId
cmsg r r2 (TyPrd rs)
  | r == r2    = prd
  | otherwise = eAbs $ \x -> hAbs prd x `mThen` mRet x
  where
    prd = mSplit $! map (hAbs . cmsg r r2) rs
cmsg r r2 (TyBrn i _ r1)
  | r == r2    = mComp next $ \ x -> mRet $ EInj i x
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

genAlt :: Prim v t => RoleId -> ATerm t v -> AType t -> TcM t (EAlt t v)
genAlt r e (TyAlt rs) = ENode <$!> mapM (genAlt r e) rs
genAlt r e r1         = ELeaf <$!> gen r e r1

gen :: Prim v t => RoleId -> ATerm t v -> AType t -> TcM t (EFun t v)
gen r p (TyAnn (TApp f a) r1) =
  appPoly f a >>= \b -> gen r p (TyAnn b r1)

gen r e r1
  | r `Set.notMember` (termRoles e `Set.union` typeRoles r1)
  = fId

gen r p a
  | Just (r1, as) <- tryChoice a
  , requiresChoice r1 a p
  = if r1 == r
    then do -- I do the choice
      -- bs <- mapM (gen r p) as
      let !rs = Set.toList $! r `Set.delete` (typeRoles a `Set.union` termRoles p)
      eAbs $ \ x -> mCh x rs $ map (hAbs . gen r p) as
    else do -- I do the branching
      eAbs $ \x -> mBrn r $ map ((`hAbs` x) . gen r p) as

gen r (AnnAlg e r2) r1
  | r == r2    = cmsg r r2 r1 `mComp` \ x -> mRet (EApp e x)
  | otherwise = cmsg r r2 r1

gen _ AnnId _ = fId

gen r (AnnComp es) r1 = go (reverse es) r1
  where
    go []    _  = fId
    go (h:t) r2 = do
      (r3, _) <- inferGTy r2 h
      gen r h r2 `mComp` hAbs (go t r3)

gen r (AnnPrj i) (TyAnn _ r1)
  | r == r1 = eAbs $ \x -> mRet (EApp (Proj i) x)
gen r (AnnPrj i) (TyPrd rs)
  | size > 1 = eAbs $ \x -> mRet (EApp (Proj n) x)
  where
    n = idxs !! fromInteger i
    idxs = scanl' (+) 0 $ map containsR rs
    size = last idxs
    containsR r'
      | r `Set.member` typeRoles r' = 1
      | otherwise                   = 0
gen _ AnnPrj{} _ = fId

gen r e@(AnnSplit ps) r1 = do
  (r2, _) <- inferGTy r1 e -- Check the output roles
  if r `Set.member` typeRoles r2
    then prd
    else eAbs $ \x -> hAbs prd x `mThen` mRet x
  where
    prd = mSplit $! map (\p -> hAbs $ gen r p r1) ps

gen _ AnnInj{} _ = fId

gen r (AnnCase es) (TyBrn i _ a) = gen r (es !! i) a
gen _ AnnCase{} _ = fail "EMonad.gen: case expression reached a non-branch type"
gen _ AnnFmap{} _ = fail "EMonad.gen: functors not (yet) supported"


--------------------------------------------------------------------------------
-- Typing endpoint code: TODO


--------------------------------------------------------------------------------
-- Prettyprinting instances

instance IsCompound (ETerm t v) where
  isCompound EVar {} = False
  isCompound EUnit{} = False
  isCompound EVal {} = False
  isCompound EPair{} = False
  isCompound EInj {} = True
  isCompound EApp {} = True

instance Prim v t => Pretty (ETerm t v) where
  pretty (EVar i) = hcat [pretty "v", pretty i]
  pretty EUnit    = parens emptyDoc
  pretty (EVal v) = pretty v
  pretty (EPair ts) = parens $! hsep $! punctuate (pretty ", ") $! map pretty ts
  pretty (EInj i t) = hsep [ hcat [pretty "inj", brackets $! pretty i]
                           , pprParens t
                           ]
  pretty (EApp e t) = hsep [pprParens e, pprParens t]

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
  pretty blck@EBnd{} = hsep [ pretty "do {"
                            , align $!
                              vsep $!
                              (punctuate (pretty ";") $! go blck)
                              ++ [pretty "}"]
                            ]
    where
      go (EBnd m1 (EAbs Nothing m2))
        = hsep [pretty "_ <-", pretty m1] : go m2
      go (EBnd m1 (EAbs (Just v1) m2))
        = hsep [ hcat [pretty "v", pretty v1]
               , pretty "<-"
               , pretty m1] : go m2
      go m
        = [pretty m]
  pretty (ESnd r t)  = hsep [pretty "send", pretty r, pprParens t]
  pretty (ERcv r)    = hsep [pretty "recv", pretty r]
  pretty (ECh t r a) = hang 2 $!
                       vsep [ hsep [ pretty "choice"
                                   , pprParens t
                                   , brackets $!
                                     hsep $!
                                     punctuate (pretty ", ") $!
                                     map pretty r
                                   ]
                            , encloseSep
                               (pretty "( ")
                               (pretty " )")
                               (pretty ", ")
                               $! map pretty a
                            ]
  pretty (EBrn r a) = hang 2 $!
                      vsep [ hsep [ pretty "branch"
                                  , pretty r
                                  ]
                           , encloseSep
                             (pretty "( ")
                             (pretty " )")
                             (pretty ", ")
                             $! map pretty a
                           ]

renderPCode :: Prim v t => Map Id (ParProg t v) -> String
renderPCode
  = renderString
  . layoutSmart defaultLayoutOptions
  . vsep
  . map pprPDefns
  . Map.toList
  where
    pprPDefns (i, p) = nest 4 $! vsep [ hsep [pretty i, pretty "="]
                                     , vsep $! map pprCRole $! Map.toList p
                                     , line
                                     ]
    pprCRole (r, m) = hsep [pretty r, pretty "|->", pretty m]
