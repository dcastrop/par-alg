module Language.Par.Prog
  ( AProg
  , ADef (..)
  , TyEnv
  , annotateProg
  , printAnnProg
  ) where

import Control.Monad.RWS.Strict
import qualified Data.Map.Strict as Map
import Data.Text.Prettyprint.Doc ( Pretty(..)
                                 , vsep
                                 , hsep
                                 , nest
                                 , line
                                 , layoutSmart
                                 , defaultLayoutOptions
                                 )
import Data.Text.Prettyprint.Doc.Render.String
import Data.List ( foldl' )

import Language.Common.Id
import Language.Alg.Syntax
import Language.Par.Role
import Language.Par.Term

data ADef t v = AnnEDef  Id (Scheme t) (ATerm t v)
  deriving Show

type AProg t v = [ADef t v]

-- XXX: hardcoded!
_MAX_UNROLL :: Int
_MAX_UNROLL = 4

annotateProg :: (Pretty v, Pretty t) => Prog t v -> (Int, TyEnv t, AProg t v)
annotateProg = (\((e, p), RgSt{ nextId = i }, _) -> (i, e, p)) . go . annotateP
  where
    go i = runRWS i _MAX_UNROLL RgSt { nextId = 0, tyEnv = Map.empty }

splitProg :: Prog t v
          -> (TyEnv t, [(Id, Scheme t, Alg t v)])
splitProg = foldl' go (Map.empty, []) . getDefns
  where
    go m (FDef i f)   = (Map.insert i (AnnF f) $ fst m, snd m)
    go m (TDef i t)   = (Map.insert i (AnnT t) $ fst m, snd m)
    go m (EDef i s f) = (fst m, (i,s,f) : snd m)
    go m (Atom i t)   = (Map.insert i (AnnA t) $ fst m, snd m)

annotateP :: (Pretty v, Pretty t)
          => Prog t v
          -> RoleGen t (TyEnv t, AProg t v)
annotateP = (\i -> (,) <$> pure (fst i) <*> go i) . splitProg
  where
    go (env, defns) = setEnv env
                      $ mapM (\(i, s, d) ->
                                 AnnEDef i s <$> annotate d
                             ) defns

printAnnProg :: (Pretty t, Pretty v) => AProg t v -> IO ()
printAnnProg
  = putStrLn
  . renderString
  . layoutSmart defaultLayoutOptions
  . vsep
  . map pretty

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance (Pretty t, Pretty v) => Pretty (ADef t v) where
  pretty (AnnEDef i s d) = nest 4 $ vsep [ hsep [ pretty "par_fun" , pretty i ]
                                         , hsep [ pretty ":" , pretty s ]
                                         , hsep [ pretty "=" , pretty d ]
                                         , line
                                         ]
