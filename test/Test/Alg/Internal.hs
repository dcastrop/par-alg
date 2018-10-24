{-# LANGUAGE OverloadedStrings #-}
module Test.Alg.Internal
  ( suite
  ) where

import Data.Text
import Test.HUnit
import Text.Parsec
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String

import Language.Alg

suite :: Test
suite = TestLabel "Internal" $
        TestList [ suitePoly
                 , suiteType
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

ppr :: Pretty a => a -> String
ppr = renderString . layoutCompact . pretty

parseP :: Text -> Either ParseError (Func String)
parseP = runParser (polyParser identifier) initialSt ""

parseT :: Text -> Either ParseError (Type String)
parseT = runParser (typeParser identifier) initialSt ""
