module Language.Alg.Internal.Parser
  ( polyParser
  , typeParser
  , algParser
  , idParser
  , identifier
  , integer
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
natural :: AlgParser Integer
natural        = Token.natural        polyLexer
integer :: AlgParser Integer
integer        = Token.integer        polyLexer
-- float          = Token.float          polyLexer
-- naturalOrFloat = Token.naturalOrFloat polyLexer
-- decimal        = Token.decimal        polyLexer
-- hexadecimal    = Token.hexadecimal    polyLexer
-- octal          = Token.octal          polyLexer
-- symbol         = Token.symbol         polyLexer
-- lexeme         = Token.lexeme         polyLexer
--whiteSpace     = Token.whiteSpace     polyLexer
parens :: AlgParser a -> AlgParser a
parens         = Token.parens         polyLexer
-- braces         = Token.braces         polyLexer
-- angles         = Token.angles         polyLexer
brackets :: AlgParser a -> AlgParser a
brackets       = Token.brackets       polyLexer
-- semi           = Token.semi           polyLexer
-- comma          = Token.comma          polyLexer
-- colon          = Token.colon          polyLexer
-- dot            = Token.dot            polyLexer
-- semiSep        = Token.semiSep        polyLexer
-- semiSep1       = Token.semiSep1       polyLexer
-- commaSep       = Token.commaSep       polyLexer
-- commaSep1      = Token.commaSep1      polyLexer

polyParser :: Show a => AlgParser a -> AlgParser (Func a)
polyParser p = singl PSum <$> try (sepBy1 pprodParser (reservedOp "+"))
  where
    pprodParser = singl PPrd <$> try (sepBy1 (simplePoly p) (reservedOp "*"))

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
typeParser p = singl TFun <$> try (sepBy1 tsumParser $ reservedOp "->")
  where
    tsumParser = singl TSum <$> sepBy1 tprodParser (reservedOp "+")
    tprodParser = singl TPrd <$> sepBy1 (simpleType p) (reservedOp "*")

singl :: ([a] -> a) -> [a] -> a
singl _f [x] = x
singl  f xs  = f xs

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
    pRec  = reserved "Rec" *> (TRec <$> simplePoly p)
    pApp  = TApp <$> simplePoly p <*> simpleType p

algParser :: Show t => AlgParser t -> AlgParser v -> AlgParser (Alg t v)
algParser pt pv
  =   singl Comp  <$> try (sepBy1 caseParser (reservedOp "."))
  <?> "Expression"
  where
    caseParser  = singl Case  <$> try (sepBy1 splitParser (reservedOp "|||"))
    splitParser = singl Split <$> try (sepBy1 (simpleAlg pt pv) (reservedOp "&&&"))


simpleAlg :: Show t => AlgParser t -> AlgParser v -> AlgParser (Alg t v)
simpleAlg pt pv
  =   try (reserved "const" *> (Const <$> aAlg pt pv))
  <|> try (reserved "rec" *> (Rec <$> brackets (polyParser pt)
                             <*> aAlg pt pv
                             <*> aAlg pt pv))
  <|> try pFmap
  <|> aAlg pt pv
  where
    pFmap = Fmap <$> (brackets $ polyParser pt) <*> aAlg pt pv

aAlg :: Show t => AlgParser t -> AlgParser v -> AlgParser (Alg t v)
aAlg pt pv
  =   try (parens (algParser pt pv))
  <|> try pVar
  <|> try pVal
  <|> try pUnit
  <|> try pId
  <|> try pProj
  <|> try pInj
  <|> try pIn
  <|> pOut
  <?> "Atomic expression"
  where
    pVar  = Var <$> idParser
    pVal  = Val <$> pv
    pUnit = parens (return Unit)
    pId   = reserved "id" >> pure Id
    pProj = reserved "proj" >> Proj <$> brackets natural
    pInj  = reserved "inj" >> Inj <$> brackets natural
    pIn   = reserved "in" >>
      In <$> option Nothing (Just <$> brackets (polyParser pt))
    pOut  = reserved "out" >>
      Out <$> option Nothing (Just <$> brackets (polyParser pt))
