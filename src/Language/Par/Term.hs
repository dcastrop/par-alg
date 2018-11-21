{-# LANGUAGE BangPatterns #-}
module Language.Par.Term
  ( ATerm (..)
  , termRoles
  , annotate
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
  | AnnPrj !Int !Int
  | AnnSplit ![ATerm t v]
  | AnnInj !Int !Int
  | AnnCase ![ATerm t v]
  | AnnFmap !(Func t) !Role !(Alg t v)
  deriving Show

termRoles :: ATerm t v -> Set RoleId
termRoles (AnnAlg _ r)    = Set.singleton r
termRoles (AnnComp es)    = Set.unions $! map termRoles es
termRoles (AnnSplit es)   = Set.unions $! map termRoles es
termRoles (AnnCase es)    = Set.unions $! map termRoles es
termRoles AnnId {}        = Set.empty
termRoles AnnPrj{}        = Set.empty
termRoles AnnInj{}        = Set.empty
termRoles (AnnFmap _ r _) = roleIds r

annT :: ([Alg t v] -> Alg t v)
     -> ([ATerm t v] -> ATerm t v)
     -> [ATerm t v]
     -> ATerm t v
annT f _g ps@(AnnAlg _ r : _)
  | Just es <- unAlg [] ps = AnnAlg (f es) r
  where
    unAlg l [] = Just $ reverse l
    unAlg l (AnnAlg x r' : ts)
      | r == r' = unAlg (x : l) ts
    unAlg _ _ = Nothing
annT _f g ts = g ts

annComp :: [ATerm t v] -> ATerm t v
annComp = annT Comp AnnComp

annSplit :: [ATerm t v] -> ATerm t v
annSplit = annT Split AnnSplit

annCase :: [ATerm t v] -> ATerm t v
annCase = annT Case AnnCase

annotate :: (Pretty v, Pretty t, Ord v, Ord t) => RoleId -> Set (Alg t v) -> Alg t v -> TcM t v (ATerm t v)
annotate r s = ann
  where
    ann t
      | t `Set.member` s = AnnAlg t <$!> newRole
    ann (Comp es    ) = annComp <$!> mapM ann es
    ann  Id           = pure AnnId
    ann (Proj i  j  ) = pure $! AnnPrj i j
    ann (Split es   ) = annSplit <$!> mapM ann es
    ann (Inj i   j  ) = pure $ AnnInj i j
    ann (Case es    ) = annCase <$!> (mapM ann es)
    ann (Fmap f e   ) = appPoly f e >>= ann
    ann t             = pure $! AnnAlg t r

---- XXX: Fixme: alternative with single role and no interactions
--annotate :: (Pretty v, Pretty t, Ord v, Ord t) => RoleId -> Set (Alg t v) -> Alg t v -> TcM t v (ATerm t v)
--annotate ri s tm = snd <$!> ann (RId ri) tm
--  where
--    ann _ t
--      | t `Set.member` s = (\r -> (RId r, AnnAlg t r)) <$!> newRole
--    ann r (Comp es    ) = go [] r (reverse es)
--      where
--        go acc rn [] = pure (rn, annComp acc)
--        go acc rn (t : ts) = do
--          (r1, x)  <- ann rn t
--          go (x:acc) r1 ts
--    ann r  Id           = pure (r, AnnId)
--    ann r (Proj i  j  ) = pure (prjR r, AnnPrj i j)
--      where
--        prjR (RPrd ts) = ts !! i
--        prjR rn        = rn
--    ann r (Split es   ) = ((\(a, b) -> (rPrd a, annSplit b)) . unzip) <$!> mapM (ann r) es
--
--    ann r (Inj i   j  ) = pure (RBrn i j r, AnnInj i j)
--    ann r (Case es    ) = ((\(a, b) -> (rAlt a, annCase b)) . unzip) <$!> mapM (ann r) es
--
--    ann r (Fmap f e   ) = appPoly f e >>= ann r
--    ann r t             = pure (RId $ oneOf r, AnnAlg t (oneOf r))
--      where
--        oneOf (RId rid) = rid
--        oneOf (RPrd xs) = oneOf $ last xs
--        oneOf (RAlt xs) = oneOf $ last xs
--        oneOf (RBrn _ _ x) = oneOf x

appPoly :: (Pretty t, Pretty v) => Func t -> Alg t v -> TcM t v (Alg t v)
appPoly  PK{}     _ = pure Id
appPoly (PV v)    t = lookupPoly v >>= (`appPoly` t)
appPoly PI        t = pure t
appPoly (PPrd ps) t
  = Split . map (\(i, x) -> x `comp` Proj i (length ps))
  . zip [0..] <$> mapM (`appPoly` t) ps
appPoly (PSum ps) t
  = Case . map (\(i, x) -> Inj i (length ps) `comp` x)
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
  pretty (AnnPrj i j)  = hcat [pretty "proj", brackets (pretty i <> pretty "," <+> pretty j)]
  pretty (AnnSplit es)
    = hang 2 $ vsep $ punctuate (pretty " &&&") $ fmap pprParens es
  pretty (AnnInj i j)   = hcat [pretty "inj", brackets (pretty i <> pretty "," <+> pretty j)]
  pretty (AnnCase es)
    = hang 2 $ vsep $ punctuate (pretty " |||") $ fmap pprParens es
  pretty (AnnFmap f r g) = hcat [ brackets ( hcat [ pprParens f
                                                  , pretty "@"
                                                  , pretty r]
                                           )
                                , pprParens g
                                ]
