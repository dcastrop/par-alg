{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
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
  ) where

import Control.Monad.RWS.Strict
import Data.Map ( Map )
import Data.List ( foldl' )
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
    pprPDefns (i, p) = nest 4 $ vsep [ hsep [pretty i, pretty "="]
                                     , vsep $ map pprCRole $ Map.toList p
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
    go (AnnEDef i _ t _) = (i,) <$> gen t emptyK (RId $ mkRole 0)
    emptyK r = do
      x <- fresh
      return $
        Map.fromList $
        map (\r1 -> (r1, EAbs x $ ERet (EVar x))) $
        roleIds r

data ETerm t v
  = EVar Int
  | EVal v
  | EPair [ETerm t v]
  | EInj Int (ETerm t v)
  | EApp (Alg t v) (ETerm t v)
  deriving Show

data EFun t v
  = EAbs Int (EMonad t v)
  deriving Show

data EMonad t v
  = ERet (ETerm t v)
  | EBnd (EMonad t v) (EFun t v)
  | ESnd RoleId (ETerm t v)
  | ETag RoleId Int -- Singleton choice, equivalent to sending (EInj i)
  | ERcv RoleId
  | ECh  (ETerm t v) RoleId [EFun t v]
  | EBrn RoleId [EMonad t v]
  deriving Show

mcomp :: EFun t v -> EFun t v -> EFun t v
mcomp (EAbs x m) f = EAbs x (EBnd m f)

app :: EFun t v -> ETerm t v -> EMonad t v
app (EAbs i m) v = go m
  where
    go (ERet v') = ERet $ sbst v'
    go (EBnd m1 f) = EBnd (go m1) (substF f)
    go (ESnd r v') = ESnd r $ sbst v'
    go m1@ETag{} = m1
    go m1@ERcv{} = m1
    go (ECh v' r fs) = ECh (sbst v') r $ map substF fs
    go (EBrn r ms) = EBrn r $ map go ms

    sbst v'@(EVar j)
     | i == j = v
     | otherwise = v'
    sbst x@EVal{} = x
    sbst (EPair es) = EPair $ map sbst es
    sbst (EInj j e) = EInj j $ sbst e
    sbst (EApp f x) = EApp f (sbst x)

    substF f@(EAbs j m1)
      | i == j = f
      | otherwise = EAbs j $ go m1

data EProg t v
  = EptEnv { getEnv :: ParProg t v }


type CodeGen = RWS () [String] Int
type ParProg t v = Map RoleId (EFun t v)

instance Fresh CodeGen where
  fresh = get >>= \i -> put (i+1) >> pure i

lookR :: RoleId -> ParProg t v -> CodeGen (EFun t v)
lookR r m
  | Just f <- Map.lookup r m = pure f
  | otherwise               = do v <- fresh
                                 pure $ EAbs v (ERet (EVar v))

ecomp :: Map RoleId (EFun t v1)
      -> Map RoleId (EFun t v1)
      -> Map RoleId (EFun t v1)
ecomp ev1 ev2
  = Map.fromList $ concatMap go $ Set.toList $ Set.unions $ map Map.keysSet [ev1, ev2]
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
  | ri == ro = fresh >>= \v -> pure $ Map.singleton ri (EAbs v (ERet (EVar v)))
  | otherwise = do x <- fresh
                   y <- fresh
                   z <- fresh
                   pure $ Map.fromList
                     [ (ri, EAbs x (ESnd ro (EVar x) `EBnd` EAbs z (ERet (EVar x))))
                     , (ro, EAbs y (ERcv ri))
                     ]
msg (RPrd as) ro
  = do es <- envs
       z  <- fresh
       (fm, vs) <- m (EVar z) es
       pure $ Map.insert ro (EAbs z $ fm (ERet $ EPair vs))
         $ foldl1 ecomp es
  where
    m z es = foldM (\ (m',rs) ev ->
                     fresh >>= \ x ->
                      pure ( EBnd (app (ev Map.! ro) z) . EAbs x . m'
                           , EVar x:rs
                           )
                  ) (id, []) es
    envs = mapM (`msg` ro) as
msg (RBrn i a) ro
  = msg a ro >>= \ ev -> Map.insert ro <$> (m <$> fresh <*> lookR ro ev) <*> pure ev
  where
    m x f = f `mcomp` EAbs x (ERet (EInj i (EVar x)))
msg t _
  = fail $ "Cannot generate code for distributed type '" ++ render t ++ "'"

type Gen t v = Role -> CodeGen (ParProg t v)

gen :: Prim v t
    => ATerm t v
    -> Gen t v
    -> Gen t v
gen (AnnAlg e r) k a = do
  m <- msg a r
  f <- (\x -> Map.singleton r (EAbs x $ ERet (EApp e (EVar x)))) <$> fresh
  c <- k (RId r)
  return $ m `ecomp` f `ecomp` c
gen AnnId k r = k r
gen (AnnComp es) k r = foldl' (flip gen) k es r
gen (AnnPrj i) k (RPrd rs)
  | length rs > (fromInteger i) = k (rs !! fromInteger i)
gen (AnnPrj i) k r@(RId ri) = do
  f <- (\x -> Map.singleton ri (EAbs x $ ERet (EApp (Proj i) (EVar x)))) <$> fresh
  (f `ecomp`) <$> k r
gen (AnnPrj _i) _k _r
  = fail $ "Panic: ill-typed term in code generation. proj[i] to a \
           \ product of size < i"
-- XXX: fix same role occurring in many branches!
-- Idea: annotate roles with "branch within split". I.e. role + context info.
-- assume end roles in "es" disjoint for the moment
gen (AnnSplit es) k r = go es []
  where
    go []     rs = k $ RPrd $ reverse rs
    go (x:xs) rs = gen x k1 r
      where
        k1 b = go xs $ b:rs
gen (AnnInj i) k r = k (RBrn (fromInteger i) r)
gen (AnnCase es) k (RBrn i r)
  | length es > i = gen (es !! i) k r
gen (AnnCase es) k (RId r)
  | length es > 1 = do
      evs <- mapM (\ e -> gen e k (RId r)) es
      let rs = concatMap Map.keys evs
      case rs of
        [] -> fail $ "Panic: empty case in code generation"
        r1:rs1 -> do
          ev <- foldM (\e r2 -> do
                         x <- fresh
                         return $
                           Map.insert r2 (EAbs x $ EBrn r $ map (getC x r2) evs) e
                     ) Map.empty rs
          x <- fresh
          (\kk -> Map.insert r kk ev) <$>
            (EAbs x <$> (ECh (EVar x) r1 <$> mapM (\(i, ev') -> getF r ev' >>= tagBr i rs1) (zip [0..] evs)))
  where
    getC x i m
      | Just c <- Map.lookup i m = app c (EVar x)
      | otherwise               = ERet $ EVar x
    getF i m
      | Just c <- Map.lookup i m = pure c
      | otherwise               = (\x -> EAbs x $ ERet $ EVar x) <$> fresh
    tagBr i rs kk = foldM (\ c r' -> do
                              x <- fresh
                              return $ EAbs x $ ETag r' i `EBnd` c) kk rs
gen (AnnCase _es) _k _r
  = fail $ "Panic: ill-typed term in code generation. case applied to a \
           \ sum of size < i"
gen AnnFmap{} _ _ = error "Panic! Unsupported annotated fmap!"

roleIds :: Role -> [RoleId]
roleIds (RId r) = [r]
roleIds (RPrd rs) = concatMap roleIds rs
roleIds (RAlt rs) = concatMap roleIds rs
roleIds (RBrn _ r) = roleIds r

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
-- sessionInfer (ERet v) = fresh >>= \l -> ForAll l (LVar l) <$> checkETerm v

--------------------------------------------------------------------------------
-- Prettyprinting instances

instance IsCompound (ETerm t v) where
  isCompound EVar {} = False
  isCompound EVal {} = False
  isCompound EPair{} = False
  isCompound EInj {} = True
  isCompound EApp {} = True

instance Prim v t => Pretty (ETerm t v) where
  pretty (EVar i) = hcat [pretty "v", pretty i]
  pretty (EVal v) = pretty v
  pretty (EPair ts) = parens $ hsep $ punctuate (pretty ", ") $ map pretty ts
  pretty (EInj i t) = hsep [ hcat [pretty "inj", brackets $ pretty i]
                           , pprParens t
                           ]
  pretty (EApp e t) = hsep [pprParens e, pprParens t]

instance Prim v t => Pretty (EFun t v) where
  pretty (EAbs i m) = hsep [ hcat [ pretty "\\"
                                  , pretty "v", pretty i
                                  , pretty "->"
                                  ]
                           , pretty m
                           ]

instance Prim v t => Pretty (EMonad t v) where
  pretty (ERet t)    = hsep [pretty "return", pprParens t]
  pretty (EBnd m f)  = hsep [pretty m, pretty ">>=", pretty f]
  pretty (ESnd r t)  = hsep [pretty "send", pretty r, pprParens t]
  pretty (ETag r i)  = hsep [pretty "tag", pretty r, pretty i]
  pretty (ERcv r)    = hsep [pretty "recv", pretty r]
  pretty (ECh t r a) = hsep [ pretty "choice"
                            , pprParens t
                            , pretty r
                            , nest 4 $
                              parens $
                              vsep $
                              punctuate (pretty ",") $
                              map pretty a
                            ]
  pretty (EBrn r a) = hsep [ pretty "branch"
                            , pretty r
                            , nest 4 $
                              parens $
                              vsep $
                              punctuate (pretty ",") $
                              map pretty a
                            ]
