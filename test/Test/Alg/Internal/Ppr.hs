module Test.Alg.Internal.Ppr
  ( suite
  )where

import Test.HUnit
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String

import Language.Alg

suite :: Test
suite = TestLabel "Ppr" $
        TestList [ testPoly
                 , testType
                 , testAlg
                 ]

helper :: Pretty a => a -> String
helper = renderString . layoutCompact . pretty

testPoly :: Test
testPoly = TestLabel "Poly" $
  TestList [ test1
           , test2
           , test3
           ]
  where
    test1 = TestCase $ assertEqual expected expected actual
      where
        expected = "K () + K a * I"
        actual = helper $ (PSum [ PK TUnit
                                , PPrd [ PK (TPrim "a")
                                       , PI
                                       ]
                                ] :: Func String)
    test2 = TestCase $ assertEqual expected expected actual
      where
        expected = "(K a + K ()) + I * I"
        actual = helper $ (PSum [ PSum [ PK (TPrim "a")
                                       , PK TUnit
                                       ]
                                , PPrd [PI, PI]
                                ] :: Func String)
    test3 = TestCase $ assertEqual expected expected actual
      where
        expected = "K a + (K () + I) * I"
        actual = helper $ (PSum [ PK (TPrim "a")
                                , PPrd [ PSum [ PK TUnit
                                              , PI
                                              ]
                                       , PI
                                       ]
                                ] :: Func String)

testType :: Test
testType = TestLabel "Type" $
  TestList [ test1
           , test2
           , test3
           ]
  where
    test1 = TestCase $ assertEqual expected expected actual
      where
        expected = "() + a * Rec F"
        actual = helper $ (TSum [ TUnit
                                , TPrd [ TPrim "a"
                                       , TRec (mkId 1 "F")
                                       ]
                                ] :: Type String)
    test2 = TestCase $ assertEqual expected expected actual
      where
        expected = "b * (a + ()) * (Rec F -> a) -> c"
        actual = helper $ (TFun [ TPrd [TPrim "b"
                                       , TSum [TPrim "a", TUnit]
                                       , TFun [TRec (mkId 1 "F") , TPrim "a"]
                                       ]
                                , TPrim "c"
                                ] :: Type String)
    test3 = TestCase $ assertEqual expected expected actual
      where
        expected = "a * b + c -> g"
        actual = helper $ (TFun [ TSum [ TPrd [TPrim "a", TPrim "b"]
                                       , TPrim "c"
                                       ]
                                , TPrim "g"
                                ] :: Type String)

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
