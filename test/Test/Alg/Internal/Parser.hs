{-# LANGUAGE OverloadedStrings #-}
module Test.Alg.Internal.Parser
  ( suite
  )where

import Data.Text

import Test.HUnit
import Text.Parsec

import Language.Alg

suite :: Test
suite = TestLabel "Parser" $
        TestList [ testPoly
                 , testType
                 -- , testAlg
                 ]

helperP :: Text -> Either ParseError (Func String)
helperP = runParser (polyParser identifier) initialSt ""

helperT :: Text -> Either ParseError (Type String)
helperT = runParser (typeParser identifier) initialSt ""

testPoly :: Test
testPoly = TestLabel "Poly" $
  TestList [ test1
           , test2
           , test3
           , test4
           ]
  where
    test1 = TestCase $ assertEqual (unpack testV) (Right expected) actual
      where
        testV = "K () + K a * I"
        actual = helperP testV
        expected = PSum [ PK TUnit
                        , PPrd [ PK (TPrim "a")
                               , PI
                               ]
                        ] :: Func String
    test2 = TestCase $ assertEqual (unpack testV) (Right expected) actual
      where
        testV = "(K a + K ()) + I * I"
        actual = helperP testV
        expected = PSum [ PSum [ PK (TPrim "a")
                               , PK TUnit
                               ]
                        , PPrd [PI, PI]
                        ] :: Func String
    test3 = TestCase $ assertEqual (unpack testV) (Right expected) actual
      where
        testV = "K a + (K () + I) * I"
        actual   = helperP testV
        expected = PSum [ PK (TPrim "a")
                        , PPrd [ PSum [ PK TUnit
                                      , PI
                                      ]
                               , PI
                               ]
                        ] :: Func String
    test4 = TestCase $ assertEqual (unpack testV) (Right expected) actual
      where
        testV = "K a + K () + I * I"
        actual = helperP testV
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
    test1 = TestCase $ assertEqual (unpack testV) (Right expect) actual
      where
        testV = "() + a * Rec F"
        actual = helperT testV
        expect = (TSum [ TUnit
                       , TPrd [ TPrim "a"
                              , TRec (mkId 1 "F")
                              ]
                       ] :: Type String)
    test2 = TestCase $ assertEqual (unpack testV) (Right expect) actual
      where
        testV = "b * (a + ()) * (Rec F -> a) -> c"
        actual = helperT testV
        expect = (TFun [ TPrd [TPrim "b"
                              , TSum [TPrim "a", TUnit]
                              , TFun [TRec (mkId 1 "F") , TPrim "a"]
                              ]
                       , TPrim "c"
                       ] :: Type String)
    test3 = TestCase $ assertEqual (unpack testV) (Right expect) actual
      where
        testV = "a * b + c -> g"
        actual = helperT testV
        expect = (TFun [ TSum [ TPrd [TPrim "a", TPrim "b"]
                              , TPrim "c"
                              ]
                       , TPrim "g"
                       ] :: Type String)

    test4 = TestCase $ assertEqual (unpack testV) (Right expect) actual
      where
        testV  = "()"
        actual = helperT testV
        expect = (TUnit :: Type String)

    test5 = TestCase $ assertEqual (unpack testV) (Right expect) actual
      where
        testV  = "F ()"
        actual = helperT testV
        expect = (TApp (mkId 1 "F") TUnit :: Type String)

    test6 = TestCase $ assertEqual (unpack testV) (Right expect) actual
      where
        testV  = "F A"
        actual = helperT testV
        expect = (TApp (mkId 1 "F") (TPrim "A") :: Type String)

{-
testAlg :: Test
testAlg = TestLabel "Alg" $
  TestList [ test1
           , test2
           ]
  where
    test1 = TestCase $ assertEqual expected expected actual
      where
        expected = "f &&& (rec [F] j k . id) ||| (h . i)"
        actual = helper $
          ( Case [ Split [ Var $ mkId 1 "f"
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
          :: Alg String Int)
    test2 = TestCase $ assertEqual expected expected actual
      where
        expected = "const (f &&& rec [F] j k) . id ||| (h . i)"
        actual = helper $
          (Comp [ Const $ Split [ Var $ mkId 1 "f"
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
          :: Alg String Int)


-}
