-- Endpoint terms: monadic language for parallel programs
module Language.Ept.EMonad
  ( ETerm(..)
  , EFun(..)
  , EMonad(..)
  , EProg(..)
  , mcomp
  , ecomp
  , msg
  ) where

import Control.Monad.RWS.Strict
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.Alg.Syntax
import Language.Alg.Internal.TcM
import Language.Alg.Internal.Ppr
import Language.Par.Role hiding ( Role )
import Language.Par.Type
import Language.SessionTypes.Common

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
  | ESnd Role (ETerm t v)
  | ERcv Role
  | ECh  (ETerm t v) Role [EFun t v]
  | EBrn Role [EMonad t v]
  deriving Show

mcomp :: EFun t v -> EFun t v -> EFun t v
mcomp (EAbs x m) f = EAbs x (EBnd m f)

app :: EFun t v -> ETerm t v -> EMonad t v
app (EAbs i m) v = go m
  where
    go (ERet v') = ERet $ sbst v'
    go (EBnd m1 f) = EBnd (go m1) (substF f)
    go (ESnd r v') = ESnd r $ sbst v'
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
  = EptEnv { getEnv :: Map RoleId (EFun t v) }


type CodeGen = RWS () [String] Int

fresh :: CodeGen Int
fresh = get >>= \i -> put (i+1) >> pure i

lookR :: RoleId -> Map RoleId (EFun t v) -> CodeGen (EFun t v)
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

msg :: Prim v t => AType t -> RoleId -> CodeGen (Map RoleId (EFun t v))
msg (TyAnn _ ri) ro
  | ri == ro = fresh >>= \v -> pure $ Map.singleton ri (EAbs v (ERet (EVar v)))
  | otherwise = do x <- fresh
                   y <- fresh
                   pure $ Map.fromList
                     [ (ri, EAbs x (ESnd ro (EVar x)))
                     , (ro, EAbs y (ERcv ri))
                     ]
msg (TyPrd as) ro
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
msg (TyBrn i _ a _) ro
  = msg a ro >>= \ ev -> Map.insert ro <$> (m <$> fresh <*> lookR ro ev) <*> pure ev
  where
    m x f = f `mcomp` EAbs x (ERet (EInj i (EVar x)))
msg t _
  = fail $ "Cannot generate code for distributed type '" ++ render t ++ "'"


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
