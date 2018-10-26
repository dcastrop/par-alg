{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Alg.Internal.TcM
  ( TcM
  , lookupVar
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
  ) where

import Control.Arrow
import Data.Text ( Text )
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as LazyMap
import Data.Set ( Set )
import qualified Data.Set as Set
import Control.Monad.RWS.Strict

import Language.Common.Id
import Language.Alg.Syntax
import qualified Language.Alg.Internal.Parser as Parser

data St t = St { nextId   :: Int
               , knownIds :: !(Map String Id)
               , fDefns   :: !(Map Id (Func t))
               , tDefns   :: !(Map Id (Type t))
               , gamma    :: !(Map Id (Scheme t))
               }

initSt :: Parser.St t -> St t
initSt s = St { nextId = Parser.nextId s
              , knownIds = Parser.knownIds s
              , fDefns = Map.empty
              , tDefns = Map.empty
              , gamma = Map.empty
              }

type TcM t = RWS () [Text] (St t)

lookupVar :: Id -> TcM t (Scheme t)
lookupVar x = Map.lookup x . gamma <$> get >>= \ i ->
  case i of
    Just sc -> return sc
    Nothing -> fail $ "Variable not in scope: " ++ getLbl x

newPoly :: Id -> Func t -> TcM t ()
newPoly i f = modify $ \st ->
  st { fDefns = Map.insert i f $ fDefns st }

newType :: Id -> Type t -> TcM t ()
newType i f = modify $ \st ->
  st { tDefns = Map.insert i f $ tDefns st }

newFun :: Id -> Scheme t -> TcM t ()
newFun i f = modify $ \st ->
  st { gamma = Map.insert i f $ gamma st }

polyDefined :: Id -> TcM t ()
polyDefined i = get >>= \st ->
  maybe (fail $ "Undefined: " ++ getLbl i)
  (const $ return ())
  $ i `Map.lookup` fDefns st

typeDefined :: Id -> TcM t ()
typeDefined i = get >>= \st ->
  maybe (fail $ "Undefined: " ++ getLbl i)
  (const $ return ())
  $ i `Map.lookup` tDefns st

exprDefined :: Id -> TcM t ()
exprDefined i = get >>= \st ->
  maybe (fail $ "Undefined: " ++ getLbl i)
  (const $ return ())
  $ i `Map.lookup` gamma st

localTc :: TcM t a -> TcM t a
localTc m = do
  st <- get
  x <- m
  put st
  return x


instance IdGen (TcM t) where
  fresh = do
    s@St{nextId=i} <- get
    put s{nextId=i+1}
    return i
  newId i = modify $ \st ->
    st { knownIds = Map.insert (getLbl i) i $ knownIds st }
  lookupId s = do
    St { knownIds = m } <- get
    return $ Map.lookup s m

class IdGen m => Generalise m a where
  genTv :: LazyMap.Map Int String -> a -> m (Set Id, a)

generalise :: Ftv t => Type t -> TcM t (Scheme t)
generalise x = uncurry ForAll <$> genTv env x
  where env = instMeta $ Set.map getLbl $ ftv x

instance Generalise m t => Generalise m (Poly t) where
  genTv env = go
    where
      go (PK t)    = second PK <$> genTv env t
      go e@PI      = pure (Set.empty, e)
      go e@PV{}    = pure (Set.empty, e)
      go e@PMeta{} = pure (Set.empty, e)
      go (PPrd t)  = (Set.unions *** PPrd) . unzip <$> mapM go t
      go (PSum t)  = (Set.unions *** PSum) . unzip <$> mapM go t

unzipT :: (a, b) -> (c, d) -> ((a,c), (b,d))
unzipT (a, b) (c, d) = ((a,c), (b,d))

instance Generalise (TcM t) (Type t) where
  genTv env = go
    where
      go e@TPrim{}   = pure (Set.empty, e)
      go v@TVar{}    = pure (Set.empty, v)
      go e@TUnit{}   = pure (Set.empty, e)
      go (TFun ts)   = (Set.unions *** TFun) . unzip <$> mapM go ts
      go (TSum ts r) = (Set.unions *** (`TSum` r)) . unzip <$> mapM go ts
      go (TPrd ts r) = (Set.unions *** (`TPrd` r)) . unzip <$> mapM go ts
      go (TApp f t)  = ((uncurry Set.union *** uncurry TApp) .) . unzipT
                       <$> genTv env f <*> go t
      go (TRec f)    = second TRec <$> genTv env f
      go (TMeta i)   = (Set.singleton &&& TVar) <$> freshId (env LazyMap.! i)

skolemise :: Ftv t => Scheme t -> TcM t (Type t)
skolemise ForAll{scVars=vs, scType=ty}
  = (`subst` ty) . Map.fromList
  <$> mapM (\i -> (getId i,) . TMeta <$> fresh) (Set.toList vs)

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
