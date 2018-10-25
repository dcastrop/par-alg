{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module Language.Alg.Internal.Ppr
  ( printProg
  ) where

import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String

import Language.Alg.Syntax

{- Aid to prettyprinting. Used to decide when to parenthesize an expression -}
class IsCompound a where
  isCompound :: a -> Bool

instance IsCompound (Poly a) where
  isCompound PSum{} = True
  isCompound PPrd{} = True
  isCompound PK{}   = True
  isCompound _      = False

instance IsCompound (Type a) where
  isCompound TPrim{}   = False
  isCompound TVar{}    = False
  isCompound TMeta{}   = False
  isCompound TUnit{}   = False
  isCompound TFun{}    = True
  isCompound TSum{}    = True
  isCompound TPrd{}    = True
  isCompound TApp{}    = True
  isCompound TRec{}    = True

instance IsCompound (Alg t v) where
  isCompound Comp{}  = True
  isCompound Split{} = True
  isCompound Case{}  = True
  isCompound Rec{}   = False
  isCompound _       = False

pprParens :: (Pretty a, IsCompound a) => a -> Doc ann
pprParens x
  | isCompound x = parens (pretty x)
  | otherwise    = pretty x

{- Preference level. Negative numbers are never parentethised. -}
newtype Lvl = Lvl { getLvl :: Int }
  deriving (Eq, Ord)

{- Aid to prettyprinting. Compare preferences of constructs. -}
class Preference a where
  prefLvl :: a -> Lvl

instance Preference (Poly a) where
  prefLvl PI     = Lvl $ -1
  prefLvl PK{}   = Lvl $ -1
  prefLvl PV{}   = Lvl $ -1
  prefLvl PPrd{} = Lvl 4
  prefLvl PSum{} = Lvl 5

instance Preference (Type a) where
  prefLvl TPrim{} = Lvl $ -1
  prefLvl TVar{}  = Lvl $ -1
  prefLvl TMeta{} = Lvl $ -1
  prefLvl TUnit   = Lvl $ -1
  prefLvl TRec{}  = Lvl 1
  prefLvl TApp{}  = Lvl 2
  prefLvl TPrd{}  = Lvl 4
  prefLvl TSum{}  = Lvl 5
  prefLvl TFun{}  = Lvl 10

instance Preference (Alg t v) where
  prefLvl Var{}   = Lvl $ -1
  prefLvl Val{}   = Lvl $ -1
  prefLvl Const{} = Lvl $ -1
  prefLvl Unit{}  = Lvl $ -1
  prefLvl Id      = Lvl $ -1
  prefLvl Proj{}  = Lvl $ -1
  prefLvl Inj{}   = Lvl $ -1
  prefLvl In{}    = Lvl $ -1
  prefLvl Out{}   = Lvl $ -1
  prefLvl Fmap{}  = Lvl $ -1
  prefLvl Rec{}   = Lvl $ -1
  prefLvl Comp{}  = Lvl  10
  prefLvl Split{} = Lvl  4
  prefLvl Case{}  = Lvl  5

prettyLvl :: (Pretty a, Preference a) => Lvl -> a -> Doc ann
prettyLvl l x
  | prefLvl x < l = pretty x
  | otherwise     = parens (pretty x)

instance (IsCompound a, Pretty a) => Pretty (Poly a) where
  pretty (PK x)      = hsep [pretty "K", aux]
    where aux = if isCompound x then parens (pretty x) else pretty x
  pretty (PV v)      = pretty v
  pretty PI          = pretty "I"
  pretty f@(PPrd fs)
    = hsep $ punctuate (pretty " *") $ fmap (prettyLvl (prefLvl f)) fs
  pretty f@(PSum fs)
    = hsep $ punctuate (pretty " +") $ fmap (prettyLvl (prefLvl f)) fs

instance Pretty a => Pretty (Type a) where
  pretty (TPrim x)   = pretty x
  pretty (TMeta x)   = hcat [pretty "?", pretty x]
  pretty (TVar x)    = pretty x
  pretty TUnit       = pretty "()"
  pretty t@(TFun ts)
    = hsep $ punctuate (pretty " ->") $ fmap (prettyLvl (prefLvl t)) ts
  pretty t@(TSum ts)
    = hsep $ punctuate (pretty " +") $ fmap (prettyLvl (prefLvl t)) ts
  pretty t@(TPrd ts)
    = hsep $ punctuate (pretty " *") $ fmap (prettyLvl (prefLvl t)) ts
  pretty (TApp f t)
    = hsep [pprParens f, pprParens t]
  pretty (TRec f)
    = hsep [pretty "Rec", pprParens f]

instance Pretty t => Pretty (Scheme t) where
  pretty ForAll{ scVars = vs
               , scType = ty
               } = hsep [ pretty "forall"
                        , hsep pvs <> pretty ","
                        , pretty ty
                        ]
    where pvs = fmap pretty $ Set.toList vs

instance (Pretty t, Pretty v) => Pretty (Alg t v) where
  pretty (Var  v)   = pretty v
  pretty (Val  v)   = pretty v
  pretty (Const c)  = hsep [pretty "const", aux $ pretty c]
    where aux = if isCompound c then parens else id
  pretty Unit       = pretty "()"
  pretty (Comp es)
    = hsep $ punctuate (pretty " .") $ fmap pprParens es
  pretty Id         = pretty "id"
  pretty (Proj i)   = hcat [pretty "proj", brackets (pretty i)]
  pretty (Split es)
    = hsep $ punctuate (pretty " &&&") $ fmap pprParens es
  pretty (Inj i)    = hcat [pretty "inj", brackets (pretty i)]
  pretty (Case es)
    = hsep $ punctuate (pretty " |||") $ fmap pprParens es
  pretty (Fmap f g) = hcat [brackets (pretty f), pprParens g]
  pretty (In f)     = hcat [pretty "in", maybe emptyDoc (brackets . pretty) f]
  pretty (Out f)    = hcat [pretty "out", maybe emptyDoc (brackets . pretty) f]
  pretty (Rec f e1 e2)
    = hsep [pretty "rec", brackets (pretty f), pprParens e1, pprParens e2]

instance (Pretty t, Pretty v) => Pretty (Def t v) where
  pretty (FDef f x)   = hsep [ pretty "poly"
                             , pretty f
                             , pretty "="
                             , pretty x
                             , pretty ";"]
  pretty (TDef f x)   = hsep [ pretty "type"
                             , pretty f
                             , pretty "="
                             , pretty x
                             , pretty ";"
                             ]
  pretty (EDef f t x) = hsep [ pretty "fun"
                             , pretty f
                             , pretty ":"
                             , pretty t
                             , pretty "="
                             , pretty x
                             , pretty ";"
                             ]
  pretty (Atom f x)   = hsep [ pretty "atom"
                             , pretty f
                             , pretty ":"
                             , pretty x
                             , pretty ";"
                             ]

instance (Pretty t, Pretty v) => Pretty (Prog t v) where
  pretty = vcat . map pretty . getDefns

printProg :: (Pretty t, Pretty v) => Prog t v -> IO ()
printProg = putStrLn . renderString . layoutSmart defaultLayoutOptions . pretty
