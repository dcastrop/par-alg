module Main where

import System.Exit

import Test.HUnit

import qualified Test.Alg

main :: IO ()
main = do
  c <- runTestTT $
      TestList [ Test.Alg.suite
               ]

  print c
  if (errors c + failures c == 0)
    then exitWith ExitSuccess
    else exitWith (ExitFailure 1)
