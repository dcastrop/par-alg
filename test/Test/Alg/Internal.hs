{-# LANGUAGE OverloadedStrings #-}
module Test.Alg.Internal
  ( suite
  ) where

import Data.Text
import qualified Data.Map.Strict as Map
import Test.HUnit
import Text.Parsec
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String

import Language.Alg

suite :: Test
suite = TestLabel "Internal" $
        TestList [ suitePoly
                 , suiteType
                 , suiteAlg
                 ]

suitePoly :: Test
suitePoly = TestList [ polyTest "K ()"
                     , polyTest "I"
                     , polyTest "F + G"
                     , polyTest "F * G"
                     , polyTest "K ()"
                     , polyTest "K A"
                     , polyTest "K (A -> B)"
                     , polyTest "K (A + B)"
                     , polyTest "K (A * B)"
                     , polyTest "K (F ())"
                     , polyTest "K (Rec F)"
                     , polyTest "F + G + H"
                     , polyTest "F + (G + H)"
                     , polyTest "(F + G) + H"
                     , polyTest "F * G * H"
                     , polyTest "(F * G) * H"
                     , polyTest "F * (G * H)"
                     , polyTest "F + G * H"
                     , polyTest "(F + G) * H"
                     , polyTest "K () + K A * I"
                     , polyTest "K () + K A * I * I"
                     , polyTest "(K () + K A) * I * I"
                     , polyTest "K () + (K A * I) * I"
                     , polyTest "K () + K A * (I * I)"
                     ]

suiteType :: Test
suiteType = TestList [ typeTest "()"
                     , typeTest "A"
                     , typeTest "A -> B"
                     , typeTest "A + B"
                     , typeTest "A * B"
                     , typeTest "F ()"
                     , typeTest "F ()"
                     , typeTest "F A"
                     , typeTest "F (A -> B)"
                     , typeTest "F (A + B)"
                     , typeTest "F (A * B)"
                     , typeTest "F (G ())"
                     , typeTest "F (Rec G)"
                     , typeTest "I ()"
                     , typeTest "(K A) ()"
                     , typeTest "(F + G) ()"
                     , typeTest "(F * G) ()"
                     , typeTest "Rec F"
                     , typeTest "Rec I"
                     , typeTest "Rec (K ())"
                     , typeTest "Rec (F + G)"
                     , typeTest "Rec (F * G)"
                     , typeTest "A + B + C"
                     , typeTest "A + (B + C)"
                     , typeTest "(A + B) + C"
                     , typeTest "A * B * C"
                     , typeTest "(A * B) * C"
                     , typeTest "A * (B * C)"
                     , typeTest "A + B * C"
                     , typeTest "(A + B) * C"
                     , typeTest "A + B * C -> D -> E"
                     , typeTest "A + B * (C -> D) -> E"
                     , typeTest "A + (B * C -> D) -> E"
                     , typeTest "(A + B * C -> D) -> E"
                     , typeTest "A + Rec F * C -> D -> E"
                     , typeTest "A + B * (Rec F -> D) -> E"
                     , typeTest "Rec F + (B * C -> D) -> E"
                     , typeTest "(A + B * C -> Rec F) -> E"
                     , typeTest "(A + B * C -> Rec F) -> Rec F"
                     ]

suiteAlg :: Test
suiteAlg = TestList [ algTest "f . g . h"
                    , algTest "f . (g . h)"
                    , algTest "(f . g) . h"
                    , algTest "f . (g &&& h)"
                    , algTest "(f . g) &&& h"
                    , algTest "f . (g ||| h)"
                    , algTest "(f . g) ||| h"
                    , algTest "rec [F] g h . (rec [F + G] h i . j)"
                    , algTest "rec [F] g h . (rec [F + G] h i . [H]j)"
                    ]

polyTest :: Text -> Test
polyTest expected =
  TestCase $ assertEqual ("[Poly] pretty . parse = id: " ++ expect) (Right expect) actual
  where
    expect = unpack expected
    actual = either Left (Right . ppr) (parseP expected)

typeTest :: Text -> Test
typeTest expected =
  TestCase $ assertEqual ("[Type] pretty . parse = id: " ++ expect) (Right expect) actual
  where
    expect = unpack expected
    actual = either Left (Right . ppr) (parseT expected)

algTest :: Text -> Test
algTest expected =
  TestCase $ assertEqual ("[Alg] pretty . parse = id: " ++ expect) (Right expect) actual
  where
    expect = unpack expected
    actual = either Left (Right . ppr) (parseA expected)

ppr :: Pretty a => a -> String
ppr = renderString . layoutCompact . pretty

parseP :: Text -> Either ParseError (Func String)
parseP = runParser (polyParser identifier) (initialSt Map.empty) ""

parseT :: Text -> Either ParseError (Type String)
parseT = runParser (typeParser identifier) (initialSt Map.empty) ""

parseA :: Text -> Either ParseError (Alg String Integer)
parseA = runParser (algParser identifier integer) (initialSt Map.empty) ""
