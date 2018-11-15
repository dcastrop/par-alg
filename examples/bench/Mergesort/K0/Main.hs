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
              , sizeLow * 32
              , sizeLow * 64
              ]
step        = sizeLow `div` 10
numSteps    = 10
randList n  = replicateM n $ randomRIO (minBound,maxBound::Int)
sizeLow     = 10000
sizeHigh    = sizeLow

main = cmain -- msMain 100000

msMain sz = do
  l <- randList sz
  t'init <- getTime Realtime
  ms l >>= ensure
  t'last <- getTime Realtime
  print $ t'last - t'init


config = defaultConfig {
            resamples = 10
         }

cmain = do
  lss <- mapM randList range >>= ensure
  defaultMainWith config
      [ bgroup "par" $ map mkMsBench lss
      , bgroup "seq" $ map mkSqBench lss
      , bgroup "std" $ map mkBench lss
      ]
  where
    mkMsBench l = bench (show $ length l) $ nfIO $ ms l
    mkSqBench l = bench (show $ length l) $ nf defn0 l
    mkBench l = bench (show $ length l) $ nf sort l
