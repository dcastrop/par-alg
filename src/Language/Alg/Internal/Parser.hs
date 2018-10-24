module Language.Alg.Internal.Parser
  ( polyParser
  , typeParser
  , idParser
  , identifier
  , initialSt
  ) where

import Control.Monad.Identity
import Data.Text ( Text )
import Data.Map ( Map )
import qualified Data.Map as Map
import Text.Parsec
import Text.Parsec.Token ( GenTokenParser
                         , GenLanguageDef(..)
                         , makeTokenParser
                         )
import qualified Text.Parsec.Token as Token

import Language.Internal.Id
import Language.Alg.Syntax

polyDef :: GenLanguageDef Text u Identity
polyDef = LanguageDef
          { commentStart    = "/*"
          , commentEnd      = "*/"
          , commentLine     = "//"
          , nestedComments  = True
          , identStart      = letter
          , identLetter     = alphaNum <|> oneOf "_'"
          , opStart         = opLetter polyDef
          , opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
          , reservedOpNames = ["*", "+", "->", "&&&", "|||"]
          , reservedNames   = ["poly", "type", "atom", "const", "id", "Rec",
                               "()", "rec", "K", "I"
                              ]
          , caseSensitive   = True
          }

data St = St { freshId  :: Int
             , foundIds :: Map String Id
             }

initialSt :: St
initialSt = St { freshId = 1
               , foundIds = Map.empty }


polyLexer :: GenTokenParser Text St Identity
polyLexer = makeTokenParser polyDef

type AlgParser = ParsecT Text St Identity

identifier :: AlgParser String
identifier     = Token.identifier     polyLexer
reserved :: String -> AlgParser ()
reserved       = Token.reserved       polyLexer
-- operator       = Token.operator       polyLexer
reservedOp :: String -> AlgParser ()
reservedOp     = Token.reservedOp     polyLexer
-- charLiteral    = Token.charLiteral    polyLexer
-- stringLiteral  = Token.stringLiteral  polyLexer
-- natural        = Token.natural        polyLexer
-- integer        = Token.integer        polyLexer
-- float          = Token.float          polyLexer
-- naturalOrFloat = Token.naturalOrFloat polyLexer
-- decimal        = Token.decimal        polyLexer
-- hexadecimal    = Token.hexadecimal    polyLexer
-- octal          = Token.octal          polyLexer
-- symbol         = Token.symbol         polyLexer
-- lexeme         = Token.lexeme         polyLexer
--whiteSpace :: AlgParser ()
--whiteSpace     = Token.whiteSpace     polyLexer
parens :: AlgParser a -> AlgParser a
parens         = Token.parens         polyLexer
-- braces         = Token.braces         polyLexer
-- angles         = Token.angles         polyLexer
-- brackets       = Token.brackets       polyLexer
-- semi           = Token.semi           polyLexer
-- comma          = Token.comma          polyLexer
-- colon          = Token.colon          polyLexer
-- dot            = Token.dot            polyLexer
-- semiSep        = Token.semiSep        polyLexer
-- semiSep1       = Token.semiSep1       polyLexer
-- commaSep       = Token.commaSep       polyLexer
-- commaSep1      = Token.commaSep1      polyLexer

polyParser :: Show a => AlgParser a -> AlgParser (Func a)
polyParser p = pSum1 <$> try (sepBy1 pprodParser (reservedOp "+"))
  where
    pprodParser = pPrd1 <$> try (sepBy1 (simplePoly p) (reservedOp "*"))
    pSum1 [x] = x
    pSum1 x   = PSum x
    pPrd1 [x] = x
    pPrd1 x   = PPrd x

simplePoly :: Show a => AlgParser a -> AlgParser (Func a)
simplePoly p
  =   try pI
  <|> try pK
  <|> try (PV <$> idParser)
  <|> parens (polyParser p)
  <?> "atomic polynomial"
  where
    pI = reserved "I" *> pure PI
    pK = reserved "K" *> pure PK <*> (simpleType p)

fresh :: AlgParser Int
fresh = do
  st@St{freshId = i} <- getState
  putState st { freshId = i }
  return i

getId :: String -> AlgParser Id
getId s = do
  st@St{ foundIds = m } <- getState
  case Map.lookup s m of
    Nothing -> do
      i <- fresh
      let x = mkId i s
      putState st
        { foundIds = Map.insert s x m
        }
      return x
    Just i  -> return i

idParser :: AlgParser Id
idParser = identifier >>= getId

typeParser :: Show a => AlgParser a -> AlgParser (Type a)
typeParser p = tFun1 <$> try (sepBy1 tsumParser $ reservedOp "->")
  where
    tsumParser = tSum1 <$> try (sepBy1 tprodParser $ reservedOp "+")
    tprodParser = tPrd1 <$> try (sepBy1 (simpleType p) $ reservedOp "*")
    tFun1 [x] = x
    tFun1 x   = TFun x
    tSum1 [x] = x
    tSum1 x   = TSum x
    tPrd1 [x] = x
    tPrd1 x   = TPrd x


simpleType :: Show a => AlgParser a -> AlgParser (Type a)
simpleType p
  =   try pUnit
  <|> try pRec
  <|> try pApp
  <|> try pPrim
  <|> parens (typeParser p)
  <?> "Atomic type"
  where
    pPrim = TPrim <$> p
    pUnit = parens (return TUnit)
    pRec  = reserved "Rec" *> (TRec <$> idParser)
    pApp  = TApp <$> idParser <*> simpleType p
