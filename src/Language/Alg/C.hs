{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Alg.C
  ( CType
  , CProg
  , X.St
  , X.TcSt
  , parseProg
  , parseFile
  , X.printProg
  ) where

import Data.Int
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc
import Text.Parsec ( choice
                   , try )

import qualified Language.Alg.Syntax as X
import qualified Language.Alg.Internal.Ppr as X
import qualified Language.Alg.Internal.Parser as X
import qualified Language.Alg.Internal.TcM as X

type CProg = X.Prog CType CVal

parseProg :: X.AlgParser CType CProg
parseProg = X.parseProg X.keyword parseVal

parseFile :: FilePath -> IO (X.St CType, CProg)
parseFile = X.parseFile keywords X.keyword parseVal

-- XXX: Stub
data CType = CInt32 | CString
  deriving (Show, Eq, Ord)

instance Pretty CType where
  pretty CInt32  = pretty "int"
  pretty CString = pretty "string"

instance X.KindChecker CType where
  checkKind _ CInt32 = return ()
  checkKind _ CString = return ()

instance X.IsCompound CType where
  isCompound _ = False

instance X.Ftv CType where
  ftv _ = Set.empty

data CVal = CInt Int32 | CStr String
  deriving (Show, Eq, Ord)

instance Pretty CVal where
  pretty (CInt i) = pretty i
  pretty (CStr i) = viaShow i

instance X.TypeOf CType CVal CType where
  getType _ (CInt _) = return CInt32
  getType _ (CStr _) = return CString


keywords :: Map String CType
keywords = Map.fromList [ ("int", CInt32)
                        , ("string", CString)
                        ]

parseVal :: X.AlgParser CType CVal
parseVal = choice [ try pCInt
                  , pCString
                  ]
  where
   pCInt    = (CInt . fromIntegral) <$> X.integer
   pCString = CStr <$> X.stringLiteral
