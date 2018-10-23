module Language.Alg.Internal.Parser
  ( polyParser
  , typeParser
  ) where

import Control.Monad.Identity
import Data.Text
import Data.Map ( Map )
import qualified Data.Map as Map
import Text.Parsec
import Text.Parsec.Expr
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

polyParser :: AlgParser a -> AlgParser (Func a)
polyParser = buildExpressionParser polyTable . simplePoly

simplePoly :: AlgParser a -> AlgParser (Func a)
simplePoly p
  =   pI
  <|> pK
  <|> parens (polyParser p)
  <?> "atomic polynomial"
  where
    pI = reserved "I" *> pure PI
    pK = reserved "K" *> pure PK <*> (simpleType p)

polyTable :: [[Operator Text St Identity (Poly a)]]
polyTable = [ [ binary "*" pPrd AssocLeft ]
            , [ binary "+" pSum AssocLeft ]
            ]

binary :: String -> (a -> a -> a) -> Assoc -> Operator Text St Identity a
binary  name fun assoc = Infix   (reservedOp name *> pure fun) assoc

--prefix :: String -> (a -> a) -> Operator Text Int Identity a
--prefix  name fun       = Prefix  (reservedOp name *> pure fun)
--
--postfix :: String -> (a -> a) -> Operator Text Int Identity a
--postfix name fun       = Postfix (reservedOp name *> pure fun)

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

typeParser :: AlgParser a -> AlgParser (Type a)
typeParser = buildExpressionParser typeTable . simpleType

simpleType :: AlgParser a -> AlgParser (Type a)
simpleType p
  =   pPrim
  <|> pUnit
  <|> pRec
  <|> parens (typeParser p)
  <?> "Atomic type"
  where
    pPrim = pure TPrim <*> try p
    pUnit = try (parens (return TUnit))
    pRec  = pure TRec <*> try (simplePoly p)


typeTable :: [[Operator Text St Identity (Type a)]]
typeTable = [ [ Prefix (pure TApp <*> (try identifier >>= getId)) ]
            , [ binary "*"  tPrd AssocLeft ]
            , [ binary "+"  tSum AssocLeft ]
            , [ binary "->" tFun AssocLeft ]
            ]
