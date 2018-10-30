{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Par.Role
  ( RoleId
  , Role (..)
  , RoleAnn (..)
  , RgSt (..)
  , TyEnv
  , TyDef (..)
  ) where

import Data.Map.Strict ( Map )
import Data.Text.Prettyprint.Doc

import Language.Alg.Internal.Ppr -- XXX;refactor! Lift part to Language.Internal.Ppr + defns in Language.Alg/Par.Internal.Ppr!

import qualified Language.SessionTypes.Common as ST
import Language.Common.Id
import Language.Alg.Syntax

type RoleId = ST.Role

data Role
  = RId RoleId       -- r1, r2 ...
  | RBrn Int Role -- branch_i R
  | RAlt [Role]      -- R1 \oplus R_2
  | RPrd [Role]      -- R1 x R2
  deriving (Eq, Show)

instance Preference Role where
  prefLvl RId{} = Lvl $ -1
  prefLvl RBrn{} = Lvl $ 1
  prefLvl RPrd{} = Lvl $ 2
  prefLvl RAlt{} = Lvl $ 3

instance Pretty Role where
  pretty (RId i) = pretty i
  pretty (RBrn i r) = hsep [ hcat [pretty "branch[", pretty i, pretty "]"]
                           , pretty r
                           ]
  pretty t@(RAlt rs)
    = hsep $ punctuate (pretty "\\/") $ fmap (prettyLvl (prefLvl t)) rs
  pretty t@(RPrd rs)
    = hsep $ punctuate (pretty "*") $ fmap (prettyLvl (prefLvl t)) rs

class RoleAnn t a where
  rAnn :: t -> Role -> Either String a
  rGet :: a -> (Role, t) -- Invariant: rAnn t r == Right a <-> rGet a = (t, r)

data TyDef t
  = AnnF (Func t) -- Functors
  | AnnT (Type t) -- Types
  | AnnA (Type t) -- Atoms

type TyEnv t = Map Id (TyDef t)

data RgSt t = RgSt { nextId :: Int
                   , tyEnv  :: !(TyEnv t)
                   }
