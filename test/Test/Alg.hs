module Test.Alg
  ( suite
  ) where

import qualified Test.Alg.Internal.Parser as Parser
import qualified Test.Alg.Internal.Ppr    as Pretty
import qualified Test.Alg.Internal        as Internal

import Test.HUnit

suite :: Test
suite = TestLabel "Alg" $
        TestList [ Parser.suite
                 , Pretty.suite
                 , Internal.suite
                 -- , testAlg
                 ]
