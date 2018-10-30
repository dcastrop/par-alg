{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Par.Type
  ( AType(..)
  , RoleAnn (..)
  ) where

import Control.Monad ( zipWithM )
import Data.Text.Prettyprint.Doc

import Language.Alg.Syntax
import Language.Alg.Internal.Ppr
import Language.Par.Role

data AType t
  = TyAnn (Type t) RoleId                              -- a@r
  | TyBrn Int [Type t] (AType t) (Either Int [Type t]) -- branch_i A b
  | TyAlt [AType t]                                    -- A \oplus B <- can only occur after case, so we must know always the number of alternatives
  | TyPrd [AType t]                                    -- A x B
  | TyApp (Func t) Role (Type t)                       -- F@R a
  | TyMeta Int                                         -- Metavar
  deriving (Eq, Show)

instance Pretty t => RoleAnn (Type t) (AType t) where
  rAnn t (RId i)
    = TyAnn <$> pure t <*> pure i
  rAnn t (RAlt rs)
    = TyAlt <$> mapM (rAnn t) rs
  rAnn (TSum ts _) (RBrn i r) | length ts > i
    = TyBrn i
      <$> pure (take i ts)
      <*> rAnn (ts !! i) r
      <*> pure (Right $ drop (i+1) ts)
  rAnn (TPrd ts _) (RPrd rs)
    | length ts == length rs
    = TyPrd <$> zipWithM rAnn ts rs
  rAnn l r
    = Left $ "Cannot annotate type '" ++ render l ++ "' with '" ++ render r ++ "'"


  rGet (TyAnn t i) = (RId i, t)
  rGet (TyBrn i x a (Left y)) = (RBrn i r, TSum (x ++ [t]) (Just y))
    where (r, t) = rGet a
  rGet (TyBrn i x a (Right y)) = (RBrn i r, TSum (x ++ t : y) Nothing)
    where (r, t) = rGet a
  rGet (TyAlt xs) = (RAlt rs, head ts)
    where (rs, ts) = unzip $ map rGet xs
  rGet (TyPrd xs) = (RPrd rs, TPrd ts Nothing)
    where (rs, ts) = unzip $ map rGet xs
  rGet (TyApp f r t) = (r, TApp f t)
  rGet TyMeta{} = error $ "Panic, ambiguous annotated type!"

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
  pretty (TyBrn i l a (Right r))
    = hsep [ hcat [ pretty ("brn[" :: String)
                  , pretty i
                  , pretty ("]" :: String)
                  ]
           , hsep $ map pprParens l
           , pprParens a
           , hsep $ map pprParens r]
  pretty (TyBrn i l a (Left r))
    = hsep [ hcat [ pretty ("brn[" :: String)
                  , pretty i
                  , pretty ("]" :: String)
                  ]
           , hsep $ map pprParens l
           , pprParens a
           , hcat [pretty ("?" :: String), pretty r]
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
