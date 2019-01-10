{-# LANGUAGE BangPatterns #-}
module Language.Par.Term
  ( ATerm (..)
  , liftAnn
  , termRoles
  , annotate
  ) where

import Control.Monad.RWS.Strict
import Data.Set ( Set )
import Data.List ( foldl' )
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
annT f _g ps
  | Just r <- containsAnn ps
  , ([(r', es)], []) <- unAlg r [] ps
  , r == r'
  = AnnAlg (f es) r
annT _f g ps = g ps

unAlg :: RoleId
      -> [(RoleId, [Alg t v])]
      -> [ATerm t v]
      -> ([(RoleId, [Alg t v])], [ATerm t v])
unAlg _ ((r,h):t) (AnnAlg x r' : ts)
  | r == r' = unAlg r ((r, h ++ [x]) : t) ts
unAlg _ l (AnnAlg x r' : ts) = unAlg r' ((r', [x]) : l) ts
unAlg ri l (AnnSplit sl : ts)
  | ([(r, l')], []) <- unAlg ri [] sl = unAlg r l (AnnAlg (Split l') r : ts)
unAlg ri l (AnnCase sl : ts)
  | ([(r, l')], []) <- unAlg ri [] sl = unAlg r l (AnnAlg (Case l') r : ts)
unAlg r l (AnnId  : ts) = unAlg r (add r Id l) ts
unAlg r l (AnnInj i j : ts) = unAlg r (add r (Inj i j) l) ts
unAlg r l (AnnPrj i j : ts) = unAlg r (add r (Proj i j) l) ts
unAlg _ l ts = (reverse l, ts)

add :: a1 -> a2 -> [(a1, [a2])] -> [(a1, [a2])]
add r t [] = [(r, [t])]
add _ t ((r, l1) : l2) = (r, l1 ++ [t]) : l2

containsAnn :: [ATerm t v] -> Maybe RoleId
containsAnn (AnnAlg _ r : _) = Just r
containsAnn (AnnSplit ts : _ )
  | Just r <- containsAnn ts = Just r
containsAnn (AnnCase ts : _ )
  | Just r <- containsAnn ts = Just r
containsAnn (_ : t) = containsAnn t
containsAnn [] = Nothing

annComp :: Prim v t => [ATerm t v] -> ATerm t v
annComp ts
  | Just r <- containsAnn ts
  , (l, t) <- unAlg r [] ts
  = ac (annC l ++ t)
  where
    ac [x] = x
    ac xs = AnnComp xs
    annC [] = []
    annC ((r, tsr) : tt) = AnnAlg (foldl' comp Id tsr) r : annC tt
annComp [t] =  t
annComp ts = AnnComp ts

annSplit :: Prim v t => [ATerm t v] -> ATerm t v
annSplit ts
  | Just r <- containsAnn ts
  , ([(r', t)], []) <- unAlg r [] ts
  = AnnAlg (Split t) r'
annSplit ts
  | length ts == 1 = head ts
  | otherwise = AnnSplit ts

annCase :: [ATerm t v] -> ATerm t v
annCase = annT Case AnnCase

--annotate :: (Pretty v, Pretty t, Ord v, Ord t) => RoleId -> Set (Alg t v) -> Alg t v -> TcM t v (ATerm t v)
--annotate r s = ann
--  where
--    ann t
--      | t `Set.member` s = AnnAlg t <$!> newRole
--    ann (Comp es    ) = annComp <$!> mapM ann es
--    ann  Id           = pure AnnId
--    ann (Proj i  j  ) = pure $! AnnPrj i j
--    ann (Split es   ) = annSplit <$!> mapM ann es
--    ann (Inj i   j  ) = pure $ AnnInj i j
--    ann (Case es    ) = annCase <$!> (mapM ann es)
--    ann (Fmap f e   ) = appPoly f e >>= ann
--    ann t             = pure $! AnnAlg t r

-- XXX: Fixme: alternative with single role and no interactions
annotate :: (Prim v t) => RoleId -> Set (Alg t v) -> Alg t v -> TcM t v (ATerm t v)
annotate ri s tm = snd <$!> ann (RId ri) tm
  where
    ann _ t
      | t `Set.member` s = (\r -> (RId r, AnnAlg t r)) <$!> newRole
    ann r (Comp es    ) = go [] r (reverse es)
      where
        go acc rn [] = pure (rn, annComp acc)
        go acc rn (t : ts) = do
          (r1, x)  <- ann rn t
          go (x:acc) r1 ts
    ann r  Id           = pure (r, AnnId)
    ann r@(RId i) t@Proj{} = pure (r, AnnAlg t i)
    ann r (Proj i  j  ) = pure (prjR r, AnnPrj i j)
      where
        prjR (RPrd ts) = ts !! i
        prjR rn        = rn
    ann r (Split es   ) = ((\(a, b) -> (rPrd a, annSplit b)) . unzip) <$!> zipWithM ann rs es
      where
        rs = case r of
               RPrd rr -> cycle rr
               _       -> repeat r

    ann r (Inj i   j  ) = pure (RBrn i j r, AnnInj i j)
    ann r (Case es    ) = ((\(a, b) -> (rAlt ri a, annCase b)) . unzip) <$!> mapM (ann r) es

    ann r (Fmap f e   ) = appPoly f e >>= ann r
    ann r t             = pure (RId $ oneOf r, AnnAlg t (oneOf r))
      where
        oneOf rr = last $ ri : (filter (/= ri) $ Set.toList $ roleIds rr)

liftAnn :: Prim v t => ATerm t v -> ATerm t v
liftAnn (AnnSplit es) = annSplit $ map liftAnn es
liftAnn (AnnComp es) = annComp $ map liftAnn es
liftAnn (AnnCase es) = annCase $ map liftAnn es
liftAnn t            = t

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
    = align $ vsep $ prepend (pretty " .") $ fmap pprParens es
  pretty (AnnPrj i j)  = hcat [pretty "proj", brackets (pretty i <> pretty "," <+> pretty j)]
  pretty (AnnSplit es)
    = align $ vsep $ prepend (pretty " &&&") $ fmap pprParens es
  pretty (AnnInj i j)   = hcat [pretty "inj", brackets (pretty i <> pretty "," <+> pretty j)]
  pretty (AnnCase es)
    = align $ vsep $ prepend (pretty " |||") $ fmap pprParens es
  pretty (AnnFmap f r g) = hcat [ brackets ( hcat [ pprParens f
                                                  , pretty "@"
                                                  , pretty r]
                                           )
                                , pprParens g
                                ]

prepend :: Doc ann -> [Doc ann] -> [Doc ann]
prepend _d [] = []
prepend _d [x] = [x]
prepend  d (x:xs) = x : map (d <+>) xs
