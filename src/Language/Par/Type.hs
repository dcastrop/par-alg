{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Par.Type
  ( AType(..)
  ) where

import Data.Text.Prettyprint.Doc

import Language.Alg.Syntax
import Language.Alg.Internal.Ppr
import Language.Par.Role

data AType t
  = TyAnn  !(Type t) !RoleId         -- a@r
  | TyBrn  !Int !Int !(AType t)      -- branch_i A b
  | TyAlt  ![AType t]                -- A \oplus B <- can only occur after case, so we must know always the number of alternatives
  | TyPrd  ![AType t]                -- A x B
  | TyApp  !(Func t) !Role !(Type t) -- F@R a
  | TyMeta !Int                      -- Metavar
  deriving (Eq, Show)

-------------------------------------------

instance IsCompound (AType t) where
  isCompound TyAnn{}  = False
  isCompound TyBrn{}  = True
  isCompound TyAlt{}  = True
  isCompound TyPrd{}  = True
  isCompound TyApp{}  = True
  isCompound TyMeta{} = False


instance Pretty t => Pretty (AType t) where
  pretty (TyAnn t r) = hcat [pprParens t, pretty ("@" :: String), pretty r]
  pretty (TyBrn i j a)
    = hsep [ hcat [ pretty ("brn[" :: String)
                  , pretty i
                  , pretty ("," :: String)
                  , pretty j
                  , pretty ("]" :: String)
                  ]
           , pprParens a
           ]
  pretty (TyAlt es)
    = hsep $ punctuate (pretty (" ||" :: String)) $ map pprParens es
  pretty (TyPrd es)
    = hsep $ punctuate (pretty (" *" :: String)) $ map pprParens es
  pretty (TyApp f r t) = hsep [ pretty ("[" :: String)
                              , pprParens f
                              , pretty ("@" :: String)
                              , pretty r
                              , pretty ("]" :: String)
                              , pprParens t
                              ]
  pretty (TyMeta i) = hcat [ pretty ("?" :: String)
                           , pretty i
                           ]
