{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Alg.Internal.Parser
  ( AlgParser
  , keyword
  , polyParser
  , typeParser
  , algParser
  , identifier
  , integer
  , stringLiteral
  , initialSt
  , testSt
  , algDef
  , functorDef
  , atomDef
  , typeDef
  , parseProg
  , St(..)
  , parseFile
  ) where

import Prelude hiding ( readFile )

import Control.Monad.Identity
import Data.List ( foldl' )
import Data.Text ( Text )
import Data.Text.IO ( readFile )
import qualified Data.Set as Set
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import System.Exit
import Text.Parsec
import Text.Parsec.Token ( GenTokenParser
                         , GenLanguageDef(..)
                         , makeTokenParser
                         )
import qualified Text.Parsec.Token as Token

import Language.Common.Id
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
          , reservedOpNames = ["*", "+", "->", "&&&", "|||" , ";", ","]
          , reservedNames   = ["poly", "type", "atom", "fun", "forall",
                                "const", "id", "Rec", "in", "out", --
                                "()", "rec", "K", "I" --
                              ]
          , caseSensitive   = True
          }

data St t = St { nextId  :: Int
               , knownIds :: Map String Id
               , externKw :: Map String t
               }
          deriving Show

testSt :: Int -> Map String Id -> Map String t -> St t
testSt i m1 m2 = St { nextId = i
                    , knownIds = m1
                    , externKw = m2
                    }

initialSt :: Map String t -> St t
initialSt m = St { nextId = 1
                 , knownIds = Map.empty
                 , externKw = m
                 }

polyLexer :: GenTokenParser Text (St t) Identity
polyLexer = makeTokenParser polyDef

type AlgParser t = ParsecT Text (St t) Identity

instance Fresh (AlgParser t) where
  fresh = do
    st@St { nextId = i } <- getState
    putState st { nextId = 1 + i }
    return i

instance IdGen (AlgParser t) where
  newId i = modifyState $ \st ->
    st { knownIds = Map.insert (getLbl i) i $ knownIds st }
  lookupId s = do
    St { knownIds = m } <- getState
    return $ Map.lookup s m

identifier ::  AlgParser t String
identifier = Token.identifier     polyLexer >>= \i -> do
  St{externKw = m} <- getState
  if Map.member i m then unexpected $ "keyword '" ++ i ++ "'"
  else return i

keyword ::  AlgParser a a
keyword = Token.identifier     polyLexer >>= \i -> do
  St{externKw = m} <- getState
  case Map.lookup i m of
    Just x -> return x
    Nothing -> fail "unknown keyword"

reserved :: String -> AlgParser t ()
reserved       = Token.reserved       polyLexer
-- operator       = Token.operator       polyLexer
reservedOp :: String -> AlgParser t ()
reservedOp     = Token.reservedOp     polyLexer
-- charLiteral    = Token.charLiteral    polyLexer
stringLiteral :: AlgParser t String
stringLiteral  = Token.stringLiteral  polyLexer
natural :: AlgParser t Integer
natural        = Token.natural        polyLexer
natInt :: AlgParser t Int
natInt        = fromInteger <$> natural
integer :: AlgParser t Integer
integer        = Token.integer        polyLexer
-- float          = Token.float          polyLexer
-- naturalOrFloat = Token.naturalOrFloat polyLexer
-- decimal        = Token.decimal        polyLexer
-- hexadecimal    = Token.hexadecimal    polyLexer
-- octal          = Token.octal          polyLexer
-- symbol         = Token.symbol         polyLexer
-- lexeme         = Token.lexeme         polyLexer
whiteSpace :: AlgParser t ()
whiteSpace     = Token.whiteSpace     polyLexer
parens :: AlgParser t a -> AlgParser t a
parens         = Token.parens         polyLexer
braces :: AlgParser t a -> AlgParser t a
braces         = Token.braces         polyLexer
-- angles         = Token.angles         polyLexer
brackets :: AlgParser t a -> AlgParser t a
brackets       = Token.brackets       polyLexer
-- semi           = Token.semi           polyLexer
-- comma          = Token.comma          polyLexer
-- colon          = Token.colon          polyLexer
-- dot            = Token.dot            polyLexer
-- semiSep        = Token.semiSep        polyLexer
-- semiSep1       = Token.semiSep1       polyLexer
-- commaSep       = Token.commaSep       polyLexer
-- commaSep1      = Token.commaSep1      polyLexer

polyParser :: Show a => AlgParser t a -> AlgParser t (Func a)
polyParser p = singl PSum <$> try (sepBy1 pprodParser (reservedOp "+"))
  where
    pprodParser = singl PPrd <$> try (sepBy1 (simplePoly p) (reservedOp "*"))

simplePoly :: Show a => AlgParser t a -> AlgParser t (Func a)
simplePoly p
  =   try pI
  <|> try pK
  <|> try (PV <$> knownIdParser)
  <|> parens (polyParser p)
  <?> "atomic polynomial"
  where
    pI = reserved "I" *> pure PI
    pK = reserved "K" *> pure PK <*> (simpleType p)

newIdParser :: AlgParser t Id
newIdParser = identifier >>= freshId

knownIdParser :: AlgParser t Id
knownIdParser = identifier >>= knownId

schemeParser :: Show a => AlgParser t a -> ParsecT Text (St t) Identity (Scheme a)
schemeParser p = ForAll <$> option Set.empty pScVars <*> typeParser p
  where
    pScVars = reserved "forall"
              *> (Set.fromList <$> many1 newIdParser)
              <* reservedOp ","

typeParser :: Show a => AlgParser t a -> AlgParser t (Type a)
typeParser p = singl TFun <$> try (sepBy1 tsumParser $ reservedOp "->")
  where
    tsumParser = singl (`TSum` Nothing) <$> sepBy1 tprodParser (reservedOp "+")
    tprodParser = singl (`TPrd` Nothing) <$> sepBy1 (simpleType p) (reservedOp "*")

singl :: ([a] -> a) -> [a] -> a
singl _f [x] = x
singl  f xs  = f xs

simpleType :: Show a => AlgParser t a -> AlgParser t (Type a)
simpleType p
  =   try pUnit
  <|> try pRec
  <|> try pApp
  <|> try pPrim
  <|> try pVar
  <|> parens (typeParser p)
  <?> "Atomic type"
  where
    pPrim = TPrim <$> p
    pVar  = TVar <$> knownIdParser
    pUnit = parens (return TUnit)
    pRec  = reserved "Rec" *> (TRec <$> simplePoly p)
    pApp  = TApp <$> simplePoly p <*> simpleType p

algParser :: Show a => Id -> AlgParser t a -> AlgParser t v -> AlgParser t (Alg a v)
algParser dn pt pv
  =   singl Comp  <$> try (sepBy1 caseParser (reservedOp "."))
  <?> "Expression"
  where
    caseParser  = singl Case  <$> try (sepBy1 sumParser (reservedOp "|||"))
    sumParser   = singl (Case . inj) <$> try (sepBy1 splitParser (reservedOp "+++"))
      where
        inj l = map (\(i, x) -> Inj i (length l) `comp` x) $ zip [0..] l
    splitParser = singl Split <$> try (sepBy1 prodParser (reservedOp "&&&"))
    prodParser = singl (Split . proj) <$> try (sepBy1 (simpleAlg dn pt pv) (reservedOp "***"))
      where
        proj l = map (\(i, x) -> x `comp` Proj i (length l)) $ zip [0..] l


simpleAlg :: Show a => Id -> AlgParser t a -> AlgParser t v -> AlgParser t (Alg a v)
simpleAlg dn pt pv
  =   try (reserved "const" *> (Const <$> aAlg dn pt pv))
  <|> try (reserved "rec" *> (Rec dn
                               <$> brackets (polyParser pt)
                               <*> aAlg dn pt pv
                               <*> aAlg dn pt pv))
  <|> try pFmap
  <|> aAlg dn pt pv
  where
    pFmap = Fmap <$> (brackets $ polyParser pt) <*> aAlg dn pt pv

aAlg :: Show a => Id -> AlgParser t a -> AlgParser t v -> AlgParser t (Alg a v)
aAlg dn pt pv
  =   try pUnit
  <|> try pId
  <|> try pProj
  <|> try pInj
  <|> try pIn
  <|> try pOut
  <|> try pVar
  <|> try pVal
  <|> parens (algParser dn pt pv)
  <?> "Atomic expression"
  where
    pVar  = Var <$> knownIdParser
    pVal  = Val <$> pv
    pUnit = parens (return Unit)
    pId   = reserved "id" >> pure Id
    pProj = reserved "proj" >>
            uncurry Proj <$> brackets ((,) <$> natInt <*> (reservedOp "," *> natInt))
    pInj  = reserved "inj" >>
            uncurry Inj <$> brackets ((,) <$> natInt <*> (reservedOp "," *> natInt))
    pIn   = reserved "in" >>
      In <$> choice [try $ brackets $ polyParser pt, PMeta <$> fresh]
    pOut  = reserved "out" >>
      Out <$> choice [try $ brackets $ polyParser pt, PMeta <$> fresh]

atomDef :: Show a => AlgParser t a -> AlgParser t (Def a v)
atomDef pt =  reserved "atom" *> pDef <* reservedOp ";"
  where pDef = Atom <$> newIdParser <*> (reservedOp ":" *> typeParser pt)

functorDef :: Show a => AlgParser t a -> AlgParser t (Def a v)
functorDef pt =  reserved "poly" *> pDef <* reservedOp ";"
  where pDef = FDef <$> newIdParser <*> (reservedOp "=" *> polyParser pt)

typeDef :: Show a => AlgParser t a -> AlgParser t (Def a v)
typeDef pt =  reserved "type" *> pDef <* reservedOp ";"
  where pDef = TDef <$> newIdParser <*> (reservedOp "=" *> typeParser pt)

algDef :: Show a => AlgParser t a -> AlgParser t v -> AlgParser t (Def a v)
algDef pt pv =  reserved "fun" *> pDef <* reservedOp ";"
  where
    pDef = do
      dn <- newIdParser
      EDef dn
        <$> (reservedOp ":" *> schemeParser pt)
        <*> (reservedOp "=" *> (algParser dn pt pv >>= renameRec))

renameRec :: Alg a v -> AlgParser t (Alg a v)
renameRec (Rec dn1 f e1 e2) = Rec dn1 f <$> doRename e1 <*> doRename e2
renameRec e = doRename e

doRename :: IdGen f => Alg t v -> f (Alg t v)
doRename (Rec dn1 f e1 e2)
  = Rec <$> rename dn1 <*> pure f <*> doRename e1 <*> doRename e2
doRename ( Const e  ) = Const <$> doRename e
doRename ( Comp es  ) = Comp <$> mapM doRename es
doRename ( Split es ) = Split <$> mapM doRename es
doRename ( Case es  ) = Case <$> mapM doRename es
doRename ( Fmap f e ) = Fmap f <$> doRename e
doRename   e@Var {}   = pure e
doRename   e@Val {}   = pure e
doRename   e@Unit{}   = pure e
doRename   e@Id{}     = pure e
doRename   e@Proj{}   = pure e
doRename   e@Inj{}    = pure e
doRename   e@In {}    = pure e
doRename   e@Out{}    = pure e


stratDef :: (Show a, Ord a, Ord v) => AlgParser t a -> AlgParser t v -> AlgParser t (Def a v)
stratDef pt pv = reserved "par" *> pDef <* reservedOp ";"
  where
    pDef = do
      pd <- newIdParser
      kd <- reservedOp "=" *> knownIdParser
      EPar pd kd
        <$> braces (foldl' RwSeq RwRefl <$> (sepBy (atomStrat kd) $ reservedOp ";"))
    atomStrat kd = choice [ try (annotations kd)
                          , unrolling ]
    annotations kd = do
      reserved "annotate"
      Annotate <$>
        braces ( foldl' (flip Set.insert) Set.empty
                 <$> (sepBy (algParser kd pt pv) $ reservedOp ";")
               )
    unrolling = do
      reserved "unroll"
      Unroll . fromInteger <$> integer

parseProg :: (Show a, Ord a, Ord v) => AlgParser t a -> AlgParser t v -> AlgParser t (Prog a v)
parseProg pt pv = whiteSpace *> (Prog <$> many1 pDef) <* eof
  where pDef = choice [ atomDef pt
                      , functorDef pt
                      , typeDef pt
                      , algDef pt pv
                      , stratDef pt pv
                      ]

parseFile :: (Show a, Show v, Ord a, Ord v)
          => Map String a
          -> AlgParser a a
          -> AlgParser a v
          -> FilePath
          -> IO (St a, Prog a v)
parseFile kw pt pv fname = do
  input <- readFile fname
  case runParser recoverState (initialSt kw) fname input of
    Left  e -> putStrLn "Parse error" >> print e >> exitWith (ExitFailure 1)
    Right x -> return x
  where
    recoverState = (\x y -> (y, x)) <$> parseProg pt pv <*> getState
