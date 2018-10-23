{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Alg.Internal.Ppr () where

import Data.Text.Prettyprint.Doc

import Language.Alg.Syntax

class IsCompound a where
  isCompound :: a -> Bool

instance IsCompound (Poly a) where
  isCompound f@PSum{} = True
  isCompound f@PPrd{} = True
  isCompound _        = False

instance IsCompound a => IsCompound (Type a) where
  isCompound (TPrim x) = isCompound x
  isCompound TUnit{}   = False
  isCompound TFun{}    = True
  isCompound TSum{}    = True
  isCompound TPrd{}    = True
  isCompound TRec{}    = True

instance Pretty a => Pretty (Poly a) where
  pretty (PK x)    = hsep [pretty "K", pretty x]
  pretty PI        = pretty "I"
  pretty (PPrd fs) = hsep $ punctuate (pretty '*') $ fmap aux fs
    where
      aux f@PSum{} = parens (pretty f)
      aux f@PPrd{} = parens (pretty f)
      aux f        = pretty f
  pretty (PSum fs) = hsep $ punctuate (pretty '+') $ fmap aux fs
    where
      aux f@PSum{} = parens (pretty f)
      aux f        = pretty f

instance Pretty a => Pretty (Type a) where
  pretty (TPrim x) = pretty x
