{-# LANGUAGE BangPatterns #-}
module Language.Par.Term
  ( ATerm (..)
  , annotate
  , unroll -- XXX!!! REFACTOR!!
  ) where

import Control.Monad.RWS.Strict
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc hiding ( annotate )

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

annotate :: (Pretty v, Pretty t, Ord v, Ord t) => RoleId -> Set (Alg t v) -> Alg t v -> TcM t (ATerm t v)
annotate r s = ann
  where
    ann t
      | t `Set.member` s = AnnAlg t <$!> newRole
    ann (Comp es    ) = AnnComp <$!> mapM ann es
    ann  Id           = pure AnnId
    ann (Proj i     ) = pure $! AnnPrj i
    ann (Split es   ) = AnnSplit <$!> mapM ann es
    ann (Inj i      ) = pure $ AnnInj i
    ann (Case es    ) = AnnCase <$!> (mapM ann es)
    ann (Fmap f e   ) = appPoly f e >>= ann
    ann t             = pure $! AnnAlg t r

unroll :: (Pretty v, Pretty t)
          => Func t
          -> Alg t v
          -> Alg t v
          -> Int
          -> TcM  t (Alg t v)
unroll f e1 e2 n
   | n <= 0     = pure $! Rec f e1 e2
   | otherwise = do
       !fm <- unroll f e1 e2 $! n-1
       !ae <- appPoly f fm
       pure $! Comp [e1, ae, e2]

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
    = hang 2 $ vsep $ punctuate (pretty " .") $ fmap pprParens es
  pretty (AnnPrj i)  = hcat [pretty "proj", brackets (pretty i)]
  pretty (AnnSplit es)
    = hang 2 $ vsep $ punctuate (pretty " &&&") $ fmap pprParens es
  pretty (AnnInj i)   = hcat [pretty "inj", brackets (pretty i)]
  pretty (AnnCase es)
    = hang 2 $ vsep $ punctuate (pretty " |||") $ fmap pprParens es
  pretty (AnnFmap f r g) = hcat [ brackets ( hcat [ pprParens f
                                                  , pretty "@"
                                                  , pretty r]
                                           )
                                , pprParens g
                                ]
