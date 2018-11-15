{-# OPTIONS_GHC -threaded #-}
module Main where

import Control.Monad
import Control.DeepSeq
import Data.List ( sort )
import Data.Vector  ( Vector )
import qualified Data.Vector as V
import System.Random ( randomRIO )
import System.Clock

import Criterion.Main
import Criterion.Types

import Mergesort

ensure :: NFData a => a -> IO a
ensure xs = xs `deepseq` return xs


range       = [ sizeLow
              , sizeLow * 2
              , sizeLow * 4
              , sizeLow * 8
              , sizeLow * 16
              ]
step        = sizeLow `div` 10
numSteps    = 10
randList n  = V.replicateM n $ randomRIO (minBound,maxBound::Int)
sizeLow     = 10000
sizeHigh    = sizeLow

main = cmain -- msMain 100000

msMain sz = do
  print "Generating \n"
  l <- randList sz
  print "Generated\n"
  t'init <- getTime Realtime
  ms l >>= ensure
  t'last <- getTime Realtime
  print $ t'last - t'init


config = defaultConfig {
            resamples = 10
         }

cmain = do
  putStrLn "Generating test cases"
  lss <- mapM randList range >>= ensure
  putStrLn "Data generated"
  defaultMainWith config
      [ bgroup "par_ms" $ map mkMsBench lss
      , bgroup "seq_ms" $ map mkSqBench lss
      -- , bgroup "Data.List.sort" $ map mkBench lss
      ]
  where
    mkMsBench l = bench (show $ V.length l) $ nfIO $ ms l
    mkSqBench l = bench (show $ V.length l) $ nf defn0 l
   --  mkBench l = bench (show $ V.length l) $ nf sort l
