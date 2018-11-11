{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
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
  , mcomp
  , ecomp
  , msg
  , gen
  , genProg
  , generate
  , renderPCode
  , roleTrack
  ) where

import Control.Arrow ( (***) )
import Control.Monad.RWS.Strict
import Data.Map ( Map )
import qualified Data.List as List
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.Common.Id
import Language.Alg.Syntax
import Language.Alg.Internal.TcM
import Language.Alg.Internal.Ppr
import Language.Par.Role
import Language.Par.Term
import Language.Par.Prog
-- import Language.SessionTypes.Common hiding (Role)

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

generate :: Prim v t => TcSt t -> AProg t v -> IO (Int, Map Id (ParProg t v))
generate tcst p = return (st, a)
  where
    (a, st, _w) = runRWS (genProg p) () (initCGSt tcst)

initCGSt :: TcSt t -> Int
initCGSt _st = 1

genProg :: Prim v t => AProg t v -> CodeGen (Map Id (ParProg t v))
genProg = mapM go >=> (pure . Map.fromList)
  where
    go (AnnEDef i _ t _) = put 1 >> (i,) <$!> gen t emptyK (RId $! mkRole 0)
    emptyK r = do
      x <- fresh
      return $!
        Map.fromList $!
        map (\r1 -> (r1, EAbs (Just x) $! ERet (EVar x))) $!
        Set.toList $
        roleIds r

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

mcomp :: EFun t v -> EFun t v -> EFun t v
mcomp (EAbs x m) f = EAbs x (eBnd m f)

eBnd :: EMonad t v -> EFun t v -> EMonad t v
eBnd m@(ERet (EApp Var{} _)) f = EBnd m f
eBnd m@(ERet (EApp Comp{} _)) f = EBnd m f
eBnd m@(ERet (EApp Split{} _)) f = EBnd m f
eBnd m@(ERet (EApp Case{} _)) f = EBnd m f
eBnd m@(ERet (EApp Fmap{} _)) f = EBnd m f
eBnd m@(ERet (EApp Rec{} _)) f = EBnd m f
eBnd   (ERet t     ) f = app f t
eBnd m (EAbs x (ERet (EVar y)))
  | x == Just y = m
eBnd (EBnd m f1)  f2   = EBnd m (f1 `mcomp` f2)
eBnd m               f = EBnd m f

app :: EFun t v -> ETerm t v -> EMonad t v
app (EAbs i m) v = go m
  where
    go (ERet v') = ERet $! sbst v'
    go (EBnd m1 f) = eBnd (go m1) (substF f)
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


type CodeGen = RWS () [String] Int
type ParProg t v = Map RoleId (EFun t v)

resetVars :: [CodeGen a] -> CodeGen [a]
resetVars [] = return []
resetVars (mh : mt) = do
  x <- get
  h <- mh
  put x
  t <- resetVars mt
  return $ h : t


instance Fresh CodeGen where
  fresh = get >>= \i -> put (i+1) >> pure i

lookR :: RoleId -> ParProg t v -> CodeGen (EFun t v)
lookR r m
  | Just f <- Map.lookup r m = pure f
  | otherwise               = do v <- fresh
                                 pure $! EAbs (Just v) (ERet (EVar v))

ecomp :: Map RoleId (EFun t v1)
      -> Map RoleId (EFun t v1)
      -> Map RoleId (EFun t v1)
ecomp ev1 ev2
  = Map.fromList $! concatMap go $! Set.toList $! Set.unions $! map Map.keysSet [ev1, ev2]
  where
    go i
      | Just f1 <- Map.lookup i ev1, Just f2 <- Map.lookup i ev2
      = [(i, f1 `mcomp` f2)]
      | Just f1 <- Map.lookup i ev1
      = [(i, f1)]
      | Just f1 <- Map.lookup i ev2
      = [(i, f1)]
      | otherwise
      = []

msg :: Prim v t => Role -> RoleId -> CodeGen (ParProg t v)
msg (RId ri) ro
  | ri == ro = fresh >>= \v -> pure $! Map.singleton ri (EAbs (Just v) (ERet (EVar v)))
  | otherwise = do x <- fresh
                   pure $! Map.fromList
                     [ (ri, EAbs (Just x) (ESnd ro (EVar x) `eBnd` EAbs Nothing (ERet (EVar x))))
                     , (ro, EAbs Nothing (ERcv ri))
                     ]
msg (RPrd as) ro
  = do es <- envs
       z  <- fresh
       (fm, vs) <- m (EVar z) es
       pure $! Map.insert ro (EAbs (Just z) $! fm (ERet $! EPair vs))
         $! foldl1 ecomp es
  where
    m z es = foldM' (\ (m',rs) ev ->
                     fresh >>= \ x ->
                      pure ( eBnd (app (ev Map.! ro) z) . EAbs (Just x) . m'
                           , EVar x:rs
                           )
                  ) (id, []) es
    envs = mapM (`msg` ro) as
msg (RBrn i a) ro
  = msg a ro >>= \ ev -> Map.insert ro <$!> (m <$!> fresh <*> lookR ro ev) <*> pure ev
  where
    m x f = f `mcomp` EAbs (Just x) (ERet (EInj i (EVar x)))
msg t _
  = fail $! "Cannot generate code for distributed type '" ++ render t ++ "'"

type Gen t v = Role -> CodeGen (ParProg t v)

remember :: Role -> CodeGen (ParProg t v, ParProg t v)
remember r = do
  x <- fresh
  (Map.fromList *** Map.fromList) . unzip <$!> mapM (go x) (Set.toList $! roleIds r)
  where
    go x r1 = do
      return $! ((r1, EAbs (Just x) (ERet (EVar x))), (r1, EAbs Nothing (ERet (EVar x))))

gen :: Prim v t
    => ATerm t v
    -> Gen t v
    -> Gen t v
gen (AnnAlg e r) k a = do
  m <- msg a r
  f <- (\x -> Map.singleton r (EAbs (Just x) $! ERet (EApp e (EVar x)))) <$!> fresh
  c <- k (RId r)
  return $! m `ecomp` f `ecomp` c
gen AnnId k r = k r
gen (AnnComp es) k r = List.foldl' (flip gen) k es r
gen (AnnPrj i) k (RPrd rs)
  | length rs > (fromInteger i) = k (rs !! fromInteger i)
gen (AnnPrj i) k r@(RId ri) = do
  f <- (\x -> Map.singleton ri (EAbs (Just x) $! ERet (EApp (Proj i) (EVar x)))) <$!> fresh
  (f `ecomp`) <$!> k r
gen (AnnPrj _i) _k _r
  = fail $! "Panic: ill-typed term in code generation. proj[i] to a \
           \ product of size < i"
-- XXX: fix same role occurring in many branches!
-- Idea: annotate roles with "branch within split". I.e. role + context info.
-- assume end roles in "es" disjoint for the moment
gen (AnnSplit es) k r = remember r >>= \(rmb, rst) -> go rst es [] >>= \k' -> return $! rmb `ecomp` k'
  where
    go _rst []     rs = k $! RPrd $! reverse rs
    go rst (x:xs) rs = gen x k1 r
      where
        k1 b = go rst xs (b:rs) >>= \k2 -> return (rst `ecomp` k2)
gen (AnnInj i) k r = k (RBrn (fromInteger i) r)
gen (AnnCase es) k (RBrn i r)
  | length es > i = gen (es !! i) k r
gen (AnnCase es) k (RId r) = do
      evs <- resetVars $! map (\ e -> gen e k (RId r)) es
      let rs = List.nub (concatMap Map.keys evs)
      ev <- foldM' (\e r2 -> do
                      x <- fresh
                      return $!
                        Map.insert r2 (EAbs (Just x) $! EBrn r $! map (getC x r2) evs) e
                  ) Map.empty rs
      case rs List.\\ [r] of
        []  -> k (RId r)
        rs1 -> do
          x <- fresh
          (\kk -> Map.insert r kk ev) <$!>
            (EAbs (Just x) <$!> (ECh (EVar x) rs1 <$!> mapM (getF r) evs))

gen (AnnCase _es) _k _r
  = fail $! "Panic: ill-typed term in code generation. case applied to a \
           \ sum of size < i"
gen AnnFmap{} _ _ = error "Panic! Unsupported annotated fmap!"

getC :: Ord k => Int -> k -> Map k (EFun t v) -> EMonad t v
getC x i m
  | Just c <- Map.lookup i m = app c (EVar x)
  | otherwise               = ERet $! EVar x

getF :: (Ord k, Fresh f) => k -> Map k (EFun t v) -> f (EFun t v)
getF i m
  | Just c <- Map.lookup i m = pure c
  | otherwise               = (\x -> EAbs (Just x) $! ERet $! EVar x) <$!> fresh

-- type Lt t = LT Id (Type t) ()
--
-- data LScheme t = LForall Id (Lt t) (Type t)
--
-- type Gamma t = Map Id (Type t)
--
-- data ESt t = ESt { nextId   :: Int
--                  , fDefns   :: !(TyEnv t)
--                  , gamma    :: !(Gamma t)
--                  }
--
-- type LtM t = RWS () [String] (ESt t)
--
-- checkETerm :: Prim t v => EMonad t v -> LtM t (t)
--
-- sessionInfer :: Prim t v => EMonad t v -> LtM t (LScheme t)
-- sessionInfer (ERet v) = fresh >>= \l -> ForAll l (LVar l) <$!> checkETerm v

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

-- XXX: Refactor somewhere!!
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
  = RAlt $! map (`roleTrack` r) es
roleTrack (AnnInj i) t
  = RBrn (fromInteger i) t
roleTrack _ _
  = error $! "Panic! Ill-typed term reached "
