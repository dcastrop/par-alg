module Language.Par.Term
  ( ATerm (..)
  , annotate
  ) where

import Control.Monad.RWS.Strict
import qualified Data.Map.Strict as Map
import Data.Text.Prettyprint.Doc ( Pretty(..)
                                 , hcat
                                 , hsep
                                 , punctuate
                                 , brackets )

import Language.Common.Id
import Language.Alg.Syntax
import Language.Alg.Internal.Ppr
import Language.Par.Role

data ATerm t v
  = AnnAlg (Alg t v) RoleId
  | AnnId
  | AnnComp [ATerm t v]
  | AnnPrj Integer
  | AnnSplit [ATerm t v]
  | AnnInj Integer
  | AnnCase [ATerm t v]
  | AnnFmap (Func t) Role (Alg t v)
  deriving Show

annotate :: (Pretty v, Pretty t) => Alg t v -> RoleGen t (ATerm t v)
annotate x = ask >>= (`ann` x)

ann :: (Pretty v, Pretty t) => Int -> Alg t v -> RoleGen t (ATerm t v)
ann i (Comp es    ) = AnnComp <$> mapM (ann i) es
ann _  Id           = pure AnnId
ann _ (Proj i     ) = pure $ AnnPrj i
ann i (Split es   ) = AnnSplit <$> mapM (ann i) es
ann _ (Inj i      ) = pure $ AnnInj i
ann i (Case es    ) = AnnCase <$> mapM (ann i) es
ann i (Fmap f e   ) = appPoly f e >>= (ann i)
ann i (Rec f e1 e2) = unrollAnn f e1 e2 i
ann _ t             = AnnAlg t . newRole <$> fresh

unrollAnn :: (Pretty v, Pretty t)
          => Func t
          -> Alg t v
          -> Alg t v
          -> Int
          -> RoleGen t (ATerm t v)
unrollAnn f e1 e2 n
   | n <= 0     = AnnAlg (Rec f e1 e2) . newRole <$> fresh
   | otherwise = appPoly f (Rec f e1 e2) >>= \ e -> ann (n-1) (Comp [e1, e, e2])


lookupPoly :: Id -> RoleGen t (Func t)
lookupPoly i = get >>= \st -> maybe err getf $ i `Map.lookup` tyEnv st
  where
    getf (AnnF f) = pure f
    getf _        = err
    err = fail $ "Undefined functor '" ++ render i ++ "'"

appPoly :: (Pretty t, Pretty v) => Func t -> Alg t v -> RoleGen t (Alg t v)
appPoly  PK{}     _ = pure Id
appPoly (PV v)    t = lookupPoly v >>= (`appPoly` t)
appPoly PI        t = pure t
appPoly (PPrd ps) t
  = Split . map (\(i, x) -> x `comp` Proj i)
  . zip [0..] <$> mapM (`appPoly` t) ps
appPoly (PSum ps) t
  = Case . map (\(i, x) -> Inj i `comp` x)
  . zip [0..] <$> mapM (`appPoly` t) ps
appPoly x@PMeta{} t = fail $ "Ambiguous type '" ++ render (Fmap x t) ++ "'"

-------------------------------------------------------------------------------

instance IsCompound (ATerm t v) where
  isCompound AnnAlg{}   = False
  isCompound AnnId{}    = False
  isCompound AnnComp{}  = True
  isCompound AnnPrj{}   = False
  isCompound AnnSplit{} = True
  isCompound AnnInj{}   = False
  isCompound AnnCase{}  = True
  isCompound AnnFmap{}  = True

instance (Pretty v, Pretty t) => Pretty (ATerm t v) where
  pretty (AnnAlg e r) = hcat [ pprParens e, pretty "@", pretty r]
  pretty AnnId        = pretty "id"
  pretty (AnnComp es)
    = hsep $ punctuate (pretty " .") $ fmap pprParens es
  pretty (AnnPrj i)  = hcat [pretty "proj", brackets (pretty i)]
  pretty (AnnSplit es)
    = hsep $ punctuate (pretty " &&&") $ fmap pprParens es
  pretty (AnnInj i)   = hcat [pretty "inj", brackets (pretty i)]
  pretty (AnnCase es)
    = hsep $ punctuate (pretty " |||") $ fmap pprParens es
  pretty (AnnFmap f r g) = hcat [ brackets ( hcat [ pprParens f
                                                  , pretty "@"
                                                  , pretty r]
                                           )
                                , pprParens g
                                ]
