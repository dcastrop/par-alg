module Language.Alg.C
  ( parseProg
  , parseFile
  , X.printProg
  ) where

import Data.Int
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import Data.Text.Prettyprint.Doc

import qualified Language.Alg.Syntax as X
import qualified Language.Alg.Internal.Ppr as X
import qualified Language.Alg.Internal.Parser as X

type CProg = X.Prog CType CVal

parseProg :: X.AlgParser CType CProg
parseProg = X.parseProg X.keyword parseVal

parseFile :: FilePath -> IO (X.St CType, CProg)
parseFile = X.parseFile keywords X.keyword parseVal

-- XXX: Stub
data CType = CInt32
  deriving Show

instance Pretty CType where
  pretty CInt32 = pretty "int"

data CVal = CInt Int32
  deriving Show

instance Pretty CVal where
  pretty (CInt i) = pretty i

keywords :: Map String CType
keywords = Map.fromList [ ("int", CInt32)
                        ]

parseVal :: X.AlgParser CType CVal
parseVal = (CInt . fromIntegral) <$> X.integer
