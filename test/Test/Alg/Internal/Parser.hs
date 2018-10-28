{-# LANGUAGE OverloadedStrings #-}
module Test.Alg.Internal.Parser
  ( suite
  )where

import Data.Text
import qualified Data.Map.Strict as Map

import Test.HUnit
import Text.Parsec

import Language.Alg

suite :: Test
suite = TestLabel "Parser" $
        TestList [ testPoly
                 , testType
                 , testAlg
                 ]

testState :: St String
testState = testSt 10 l Map.empty
  where l = Map.fromList
            [ ("f", mkId 1 "f")
            , ("g", mkId 2 "g")
            , ("h", mkId 3 "h")
            , ("F", mkId 4 "F")
            , ("G", mkId 5 "G")
            , ("H", mkId 6 "H")
            , ("i", mkId 7 "i")
            , ("j", mkId 8 "j")
            , ("k", mkId 9 "k")
            ]

helperP :: Text -> Either ParseError (Func String)
helperP = runParser (polyParser identifier) testState ""

helperT :: Text -> Either ParseError (Type String)
helperT = runParser (typeParser identifier) testState ""

helperA :: Text -> Either ParseError (Alg String Integer)
helperA = runParser (algParser identifier integer) testState ""

testPoly :: Test
testPoly = TestLabel "Poly" $
  TestList [ test1
           , test2
           , test3
           , test4
           ]
  where
    test1 = TestCase $ assertEqual (unpack testV) (show expected) actual
      where
        testV = "K () + K a * I"
        actual = either show show $ helperP testV
        expected = PSum [ PK TUnit
                        , PPrd [ PK (TPrim "a")
                               , PI
                               ]
                        ] :: Func String
    test2 = TestCase $ assertEqual (unpack testV) (show expected) actual
      where
        testV = "(K a + K ()) + I * I"
        actual = either show show $ helperP testV
        expected = PSum [ PSum [ PK (TPrim "a")
                               , PK TUnit
                               ]
                        , PPrd [PI, PI]
                        ] :: Func String
    test3 = TestCase $ assertEqual (unpack testV) (show expected) actual
      where
        testV = "K a + (K () + I) * I"
        actual   = either show show $ helperP testV
        expected = PSum [ PK (TPrim "a")
                        , PPrd [ PSum [ PK TUnit
                                      , PI
                                      ]
                               , PI
                               ]
                        ] :: Func String
    test4 = TestCase $ assertEqual (unpack testV) (show expected) actual
      where
        testV = "K a + K () + I * I"
        actual = either show show $ helperP testV
        expected = PSum [ PK (TPrim "a")
                        , PK TUnit
                        , PPrd [PI, PI]
                        ] :: Func String
testType :: Test
testType = TestLabel "Type" $
  TestList [ test1
           , test2
           , test3
           , test4
           , test5
           , test6
           ]
  where
    test1 = TestCase $ assertEqual (unpack testV) (show expect) actual
      where
        testV = "() + a * Rec F"
        actual = either show show $ helperT testV
        expect = (TSum [ TUnit
                       , TPrd [ TPrim "a"
                              , TRec (PV $ mkId 1 "F")
                              ] Nothing
                       ] Nothing :: Type String)
    test2 = TestCase $ assertEqual (unpack testV) (show expect) actual
      where
        testV = "b * (a + ()) * (Rec F -> a) -> c"
        actual = either show show $ helperT testV
        expect = (TFun [ TPrd [TPrim "b"
                              , TSum [TPrim "a", TUnit] Nothing
                              , TFun [TRec (PV $ mkId 1 "F") , TPrim "a"]
                              ] Nothing
                       , TPrim "c"
                       ] :: Type String)
    test3 = TestCase $ assertEqual (unpack testV) (show expect) actual
      where
        testV = "a * b + c -> g"
        actual = either show show $ helperT testV
        expect = (TFun [ TSum [ TPrd [TPrim "a", TPrim "b"] Nothing
                              , TPrim "c"
                              ] Nothing
                       , TPrim "g"
                       ] :: Type String)

    test4 = TestCase $ assertEqual (unpack testV) (show expect) actual
      where
        testV  = "()"
        actual = either show show $ helperT testV
        expect = (TUnit :: Type String)

    test5 = TestCase $ assertEqual (unpack testV) (show expect) actual
      where
        testV  = "F ()"
        actual = either show show $ helperT testV
        expect = (TApp (PV $ mkId 1 "F") TUnit :: Type String)

    test6 = TestCase $ assertEqual (unpack testV) (show expect) actual
      where
        testV  = "F A"
        actual = either show show $ helperT testV
        expect = (TApp (PV $ mkId 1 "F") (TPrim "A") :: Type String)

mkATest :: Text -> Alg String Integer -> Test
mkATest t a = TestCase $ assertEqual (unpack t) expect actual
  where
    expect = show a
    actual = either show show $ helperA t

testAlg :: Test
testAlg = TestLabel "Alg" $
  TestList
  [ mkATest "f" (Var $ mkId 1 "f")
  , mkATest "f . g . h" $
    Comp [ Var $ mkId 1 "f"
         , Var $ mkId 1 "g"
         , Var $ mkId 1 "h"
         ]
  , mkATest "f . (g . h)" $
    Comp [ Var $ mkId 1 "f"
         , Comp [ Var $ mkId 1 "g"
                , Var $ mkId 1 "h"
                ]
         ]
  , mkATest "(f . g) . h" $
    Comp [ Comp [ Var $ mkId 1 "f"
                , Var $ mkId 1 "g"
                ]
         , Var $ mkId 1 "h"
         ]
  , mkATest "const 1" $
    Const (Val 1)
  , mkATest "rec[F] f g" $
    Rec (PV $ mkId 1 "F") (Var $ mkId 1 "f") (Var $ mkId 1 "g")
  , mkATest "[F] f" $
    Fmap (PV $ mkId 1 "F") (Var $ mkId 1 "f")
  , mkATest "f . (g &&& h)" $
    Comp [ Var $ mkId 1 "f"
         , Split [ Var $ mkId 1 "g"
                 , Var $ mkId 1 "h"
                 ]
         ]
  , mkATest "(f . g) &&& h" $
    Split [ Comp [ Var $ mkId 1 "f"
                 , Var $ mkId 1 "g"
                 ]
          , Var $ mkId 1 "h"
          ]
  , mkATest "(f &&& (rec [F] j k . id)) ||| (h . i)" $
    Case [ Split [ Var $ mkId 1 "f"
                 , Comp [ Rec (PV $ mkId 1 "F")
                          (Var $ mkId 1 "j")
                          (Var $ mkId 1 "k")
                        , Id
                        ]
                 ]
         , Comp [ Var $ mkId 1 "h"
                , Var $ mkId 1 "i"
                ]
         ]
  , mkATest "const (f &&& rec [F] j k) . (id ||| (h . i))" $
    Comp [ Const $ Split [ Var $ mkId 1 "f"
                         , Rec (PV $ mkId 1 "F")
                           (Var $ mkId 1 "j")
                           (Var $ mkId 1 "k")
                         ]
         , Case [ Id
                , Comp [ Var $ mkId 1 "h"
                       , Var $ mkId 1 "i"
                       ]
                ]
         ]
  ]
