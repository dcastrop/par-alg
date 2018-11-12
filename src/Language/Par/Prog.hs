module Language.Par.Prog
  ( AProg
  , ADef (..)
  , AnnScheme (..)
  , renderProg
  , GTy
  , Global (..)
  , gRoles
  ) where

import Data.Text.Prettyprint.Doc ( Pretty(..)
                                 , vsep
                                 , hsep
                                 , nest
                                 , hcat
                                 , emptyDoc
                                 , space
                                 , line
                                 , punctuate
                                 , layoutSmart
                                 , defaultLayoutOptions
                                 )
import Data.Text.Prettyprint.Doc.Render.String
import Data.Set ( Set )
import qualified Data.Set as Set

import Language.SessionTypes.Global
import Language.Common.Id
import Language.Alg.Syntax
import Language.Par.Role
import Language.Par.Term
import Language.Par.Type

data AnnScheme a
  = AForAll { ascVars :: !(Set Id)
            , ascDom :: !(AType a)
            , ascCod :: !(AType a)
            }
  deriving (Eq, Show)

instance Pretty t => Pretty (AnnScheme t) where
  pretty AForAll{ ascVars = vs
                , ascDom = aty
                , ascCod = bty
                } = hcat [ pForAll
                        , pretty aty
                        , pretty " -> "
                        , pretty bty
                        ]
    where pvs = fmap pretty $! Set.toList vs
          pForAll
            | Set.null vs = emptyDoc
            | otherwise   = hsep [pretty "forall" , hsep pvs <> pretty ",", space]

data ADef t v = AnnEDef  !Id !(AnnScheme t) !(ATerm t v) !(Global t)
  deriving Show

type AProg t v = [ADef t v]

renderProg :: (Pretty t, Pretty v) => AProg t v -> String
renderProg
  = renderString
  . layoutSmart defaultLayoutOptions
  . vsep
  . map pretty

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance (Pretty t, Pretty v) => Pretty (ADef t v) where
  pretty (AnnEDef i s d g) = nest 4 $! vsep [ hsep [ pretty "par_fun" , pretty i ]
                                           , hsep [ pretty ":" , pretty s ]
                                           , hsep [ pretty "=" , pretty d ]
                                           , hsep [ pretty "~" , pretty g ]
                                           , line
                                           ]
type GTy t = GT Int (Type t) ()

data Global t
  = Leaf !(GTy t)
  | Brn  ![Global t]
  | BSeq ![Global t] ![GTy t]
  deriving Show

gRoles :: Global t -> Set RoleId
gRoles (Leaf g) = getRoles g
gRoles (Brn gs) = Set.unions $! map gRoles gs
gRoles (BSeq gs gt) = Set.unions $! map gRoles gs ++ map getRoles gt

instance Pretty t => Pretty (Global t) where
  pretty (Leaf g) = pretty g
  pretty (Brn gs) = hsep [ pretty "alts ["
                         , vsep $! punctuate (pretty ",") $! map pretty gs
                         , pretty "]" ]
  pretty (BSeq gs gt) = hsep [pretty (Brn gs), pretty ";", pretty $ GSeq gt]
