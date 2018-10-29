{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Alg.C
  ( CType
  , CProg
  , X.St
  , X.TcSt
  , parseProg
  , parseFile
  , typecheck
  , X.printProg
  ) where

import Data.Int
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc

import qualified Language.Alg.Syntax as X
import qualified Language.Alg.Internal.Ppr as X
import qualified Language.Alg.Internal.Parser as X
import qualified Language.Alg.Internal.TcM as X
import qualified Language.Alg.Typecheck as X

type CProg = X.Prog CType CVal

typecheck :: X.St CType -> CProg -> IO CProg
typecheck s p = X.runTcM s (X.checkProg p)

parseProg :: X.AlgParser CType CProg
parseProg = X.parseProg X.keyword parseVal

parseFile :: FilePath -> IO (X.St CType, CProg)
parseFile = X.parseFile keywords X.keyword parseVal

-- XXX: Stub
data CType = CInt32
  deriving (Show, Eq)

instance Pretty CType where
  pretty CInt32 = pretty "int"

instance X.KindChecker CType where
  checkKind _ CInt32 = return ()

instance X.IsCompound CType where
  isCompound _ = False

instance X.Ftv CType where
  ftv _ = Set.empty

data CVal = CInt Int32
  deriving Show

instance Pretty CVal where
  pretty (CInt i) = pretty i

instance X.TypeOf CType CVal CType where
  getType _ (CInt _) = return CInt32


keywords :: Map String CType
keywords = Map.fromList [ ("int", CInt32)
                        ]

parseVal :: X.AlgParser CType CVal
parseVal = (CInt . fromIntegral) <$> X.integer
