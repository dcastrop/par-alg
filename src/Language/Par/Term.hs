module Language.Par.Term
  ( ATerm (..)
  , annotate
  ) where

import Control.Monad.RWS.Strict
import Data.Text.Prettyprint.Doc ( Pretty(..)
                                 , hcat
                                 , hsep
                                 , punctuate
                                 , brackets )

import Language.Alg.Syntax
import Language.Alg.Internal.Ppr
import Language.Alg.Internal.TcM
import Language.Par.Role

data ATerm t v
  = AnnAlg !(Alg t v) !RoleId
  | AnnId
  | AnnComp ![ATerm t v]
  | AnnPrj !Integer
  | AnnSplit ![ATerm t v]
  | AnnInj !Integer
  | AnnCase ![ATerm t v]
  | AnnFmap !(Func t) !Role !(Alg t v)
  deriving Show

annotate :: (Pretty v, Pretty t) => Alg t v -> TcM t (ATerm t v)
annotate (Comp es    ) = AnnComp <$> mapM annotate es
annotate  Id           = pure AnnId
annotate (Proj i     ) = pure $ AnnPrj i
annotate (Split es   ) = AnnSplit <$> mapM annotate es
annotate (Inj i      ) = pure $ AnnInj i
annotate (Case es    ) = AnnCase <$> mapM annotate es
annotate (Fmap f e   ) = appPoly f e >>= annotate
annotate (Rec f e1 e2) = ask >>= unrollAnnotate f e1 e2
annotate t             = AnnAlg t <$> newRole

unrollAnnotate :: (Pretty v, Pretty t)
          => Func t
          -> Alg t v
          -> Alg t v
          -> Int
          -> TcM t (ATerm t v)
unrollAnnotate f e1 e2 n
   | n <= 0     = AnnAlg (Rec f e1 e2) <$> newRole
   | otherwise = do
       ae1 <- annotate e1
       ae2 <- annotate e2
       ae  <- annApp f (unrollAnnotate f e1 e2 (n-1))
       pure $ AnnComp [ae1, ae, ae2]

acomp :: ATerm t v -> ATerm t v -> ATerm t v
acomp (AnnComp es1) (AnnComp es2) = AnnComp $ es1 ++ es2
acomp (AnnComp es1) e = AnnComp $ es1 ++ [e]
acomp e (AnnComp es2) = AnnComp $ e : es2
acomp e1 e2 = AnnComp [e1, e2]

annApp :: (Pretty t, Pretty v) => Func t -> TcM t (ATerm t v) -> TcM t (ATerm t v)
annApp  PK{}     _ = pure AnnId
annApp (PV v)    t = lookupPoly v >>= (`annApp` t)
annApp PI        t = t
annApp (PPrd ps) t
  = AnnSplit . map (\(i, x) -> x `acomp` AnnPrj i)
  . zip [0..] <$> mapM (`annApp` t) ps
annApp (PSum ps) t
  = AnnCase . map (\(i, x) -> AnnInj i `acomp` x)
  . zip [0..] <$> mapM (`annApp` t) ps
annApp x@PMeta{} _ = fail $ "Ambiguous type '" ++ render x ++ "'"

appPoly :: (Pretty t, Pretty v) => Func t -> Alg t v -> TcM t (Alg t v)
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
