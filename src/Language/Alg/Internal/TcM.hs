{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Alg.Internal.TcM
  ( TcM
  , TcSt (..)
  , newRole
  , newVar
  , sameVar
  , altRole
  , execTcM
  , runTcM
  , lookupVar
  , lookupPoly
  , localTc
  , initSt
  , generalise
  , skolemise
  , newPoly
  , newType
  , newFun
  , polyDefined
  , typeDefined
  , exprDefined
  , foldM'
  , (<$!>)
  , TypeOf (..)
  , KindChecker (..)
  , Prim
  ) where

import Prelude hiding ( putStrLn )

import Control.Arrow
--import Data.Text ( Text )
--import Data.Text.IO ( putStrLn )
import Data.Text.Prettyprint.Doc
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as LazyMap
import Data.Set ( Set )
import qualified Data.Set as Set
import Control.Monad.RWS.Strict

import Language.SessionTypes.Common

import Language.Common.Id
import Language.Common.Subst
import Language.Alg.Syntax
import Language.Alg.Internal.Ppr
import qualified Language.Alg.Internal.Parser as Parser
import Language.Alg.Internal.Ppr ( render )

foldM' :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldM' _ z [] = return z
foldM' f z (x:xs) = do
  z' <- f z x
  z' `seq` foldM' f z' xs

data TcSt t = TcSt { nextId   :: Int
                   , nextRole :: Int
                   , nextVar  :: Int
                   , knownIds :: !(Map String Id)
                   , fDefns   :: !(Map Id (Func t))
                   , tDefns   :: !(Map Id (Type t))
                   , gamma    :: !(Map Id (Scheme t))
                   }

initSt :: Parser.St t -> TcSt t
initSt s = TcSt { nextId = Parser.nextId s
                , nextRole = 1
                , nextVar = 0
                , knownIds = Parser.knownIds s
                , fDefns = Map.empty
                , tDefns = Map.empty
                , gamma = Map.empty
                }

newRole :: TcM t Role
newRole = do
  st@TcSt { nextRole = i } <- get
  put st { nextRole = i + 1 }
  return $! Rol i

newVar :: TcM t Int
newVar = do
  st@TcSt { nextVar = i } <- get
  put st { nextVar = i + 1 }
  return i

sameVar :: TcM t Int
sameVar = do
  TcSt { nextVar = i } <- get
  return i

altRole :: [TcM t a] -> TcM t [a]
altRole = foldM' go [] . reverse
  where
    go l m = do
      st@TcSt{ nextRole = i } <- get
      x <- m
      put st { nextRole = i }
      return $ x : l

type TcM t = RWS () () (TcSt t)

execTcM :: Parser.St t -> TcM t a -> IO (TcSt t)
execTcM s m = {- mapM_ putStrLn w *> -} pure st
  where (st, _w) = execRWS m () (initSt s)

runTcM :: Parser.St t -> TcM t a -> IO (a, TcSt t)
runTcM s m = {- mapM_ putStrLn w *> -} pure (a, st)
  where (a, st, _w) = runRWS m () (initSt s)

lookupVar :: Id -> TcM t (Scheme t)
lookupVar x = Map.lookup x . gamma <$!> get >>= \ i ->
  case i of
    Just sc -> return sc
    Nothing -> fail $! "Variable not in scope: " ++ getLbl x


newPoly :: Id -> Func t -> TcM t ()
newPoly i f = modify $! \st ->
  st { fDefns = Map.insert i f $! fDefns st }

newType :: Id -> Type t -> TcM t ()
newType i f = modify $! \st ->
  st { tDefns = Map.insert i f $! tDefns st }

newFun :: Id -> Scheme t -> TcM t ()
newFun i f = modify $! \st ->
  st { gamma = Map.insert i f $! gamma st }

polyDefined :: Id -> TcM t ()
polyDefined i = get >>= \st ->
  maybe (fail $! "Undefined functor: " ++ render i)
  (const $! return ())
  $! i `Map.lookup` fDefns st

lookupPoly :: Id -> TcM t (Func t)
lookupPoly i = get >>= \st ->
  maybe (fail $! "Undefined functor '" ++ render i ++ "'") pure
  $! i `Map.lookup` fDefns st

typeDefined :: Id -> TcM t ()
typeDefined i = get >>= \st ->
  maybe (fail $! "Undefined type: " ++ render i)
  (const $! return ())
  $! i `Map.lookup` tDefns st

exprDefined :: Id -> TcM t ()
exprDefined i = get >>= \st ->
  maybe (fail $! "Undefined expression: " ++ render i)
  (const $! return ())
  $! i `Map.lookup` gamma st

localTc :: TcM t a -> TcM t a
localTc m = do
  st <- get
  x <- m
  put st
  return x

instance Fresh (TcM t) where
  fresh = do
    s@TcSt{nextId=i} <- get
    put s{nextId=i+1}
    return i

instance IdGen (TcM t) where
  newId i = modify $! \st ->
    st { knownIds = Map.insert (getLbl i) i $! knownIds st }
  lookupId s = do
    TcSt { knownIds = m } <- get
    return $! Map.lookup s m

class IdGen m => Generalise m a where
  genTv :: LazyMap.Map Int String -> a -> m (Set Id, a)

generalise :: Ftv t => Type t -> TcM t (Scheme t)
generalise x = uncurry ForAll <$!> genTv env x
  where env = instMeta $! Set.map getLbl $! ftv x

instance Generalise m t => Generalise m (Poly t) where
  genTv env = go
    where
      go (PK t)    = second PK <$!> genTv env t
      go e@PI      = pure (Set.empty, e)
      go e@PV{}    = pure (Set.empty, e)
      go e@PMeta{} = pure (Set.empty, e)
      go (PPrd t)  = (Set.unions *** PPrd) . unzip <$!> mapM go t
      go (PSum t)  = (Set.unions *** PSum) . unzip <$!> mapM go t

unzipT :: (a, b) -> (c, d) -> ((a,c), (b,d))
unzipT (a, b) (c, d) = ((a,c), (b,d))

instance Generalise (TcM t) (Type t) where
  genTv env = go
    where
      go e@TPrim{}   = pure (Set.empty, e)
      go v@TVar{}    = pure (Set.empty, v)
      go e@TUnit{}   = pure (Set.empty, e)
      go (TFun ts)   = (Set.unions *** TFun) . unzip <$!> mapM go ts
      go (TSum ts r) = (Set.unions *** (`TSum` r)) . unzip <$!> mapM go ts
      go (TPrd ts r) = (Set.unions *** (`TPrd` r)) . unzip <$!> mapM go ts
      go (TApp f t)  = ((uncurry Set.union *** uncurry TApp) .) . unzipT
                       <$!> genTv env f <*> go t
      go (TRec f)    = second TRec <$!> genTv env f
      go (TMeta i)   = (Set.singleton &&& TVar) <$!> freshId (env LazyMap.! i)

skolemise :: Ftv t => Scheme t -> TcM t (Type t)
skolemise ForAll{scVars=vs, scType=ty}
  = (`subst` ty) . Map.fromList
  <$!> mapM (\i -> (getId i,) . TMeta <$!> fresh) (Set.toList vs)

tyVarSupplier :: Set String -> [String]
tyVarSupplier fvs
  = [ s
    | c <- ['a'..'z']
    , let s = [c]
            , s `Set.notMember` fvs
    ]
    ++
    [ s
    | i <- [(1::Integer)..]
    , c <- ['a'..'z']
    , let s = c : show i
            , s `Set.notMember` fvs
    ]

instMeta :: Set String -> LazyMap.Map Int String
instMeta fvs = LazyMap.fromList $ zip [0..] sup
  where sup = tyVarSupplier fvs

class TypeOf t v a | a -> t where
  getType :: Env (Type a) -> v -> TcM t a

class KindChecker t where
  checkKind :: Set Id -> t -> TcM a ()

type Prim v t = ( KindChecker t
                , Eq t
                , Pretty t
                , Pretty v
                , Ftv t
                , IsCompound t
                , Ord v
                , Ord t
                , TypeOf t v t)

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
