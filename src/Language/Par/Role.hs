{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Par.Role
  ( RoleId
  , mkRole
  , roleIds
  , Role (..)
  , rAlt
  ) where

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Text.Prettyprint.Doc
import Language.Alg.Internal.Ppr -- XXX;refactor! Lift part to Language.Internal.Ppr + defns in Language.Alg/Par.Internal.Ppr!
import qualified Language.SessionTypes.Common as ST

type RoleId = ST.Role

mkRole :: Int -> RoleId
mkRole = ST.Rol

data Role
  = RId RoleId       -- r1, r2 ...
  | RBrn Int Role -- branch_i R
  | RAlt [Role]      -- R1 \oplus R_2
  | RPrd [Role]      -- R1 x R2
  deriving (Eq, Show)

roleIds :: Role -> Set RoleId
roleIds (RId i) = Set.singleton i
roleIds (RBrn _ r) = roleIds r
roleIds (RAlt rs) = Set.unions $! map roleIds rs
roleIds (RPrd rs) = Set.unions $! map roleIds rs

rAlt :: [Role] -> Role
rAlt (r:rs)
  | all (== r) rs = r
rAlt [r] = r
rAlt rs  = RAlt rs

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
