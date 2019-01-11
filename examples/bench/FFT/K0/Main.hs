{-# OPTIONS_GHC -threaded #-}
module Main where

import Data.Complex
import Control.Monad
import Control.DeepSeq
import Data.List ( sort )
import Data.Vector  ( Vector )
import qualified Data.Vector as V
import System.Random ( randomRIO )
import Statistics.Types
import System.Clock

import Criterion.Main
import Criterion.Types

import AlgPrelude
import FFT

ensure :: NFData a => a -> IO a
ensure xs = xs `deepseq` return xs


range       = [ 2 ^ sizeLow
              , 2 ^ (sizeLow + 1)
              , 2 ^ (sizeLow + 2)
              , 2 ^ (sizeLow + 3)
              , 2 ^ (sizeLow + 4)
              , 2 ^ (sizeLow + 5)
              , 2 ^ (sizeLow + 6)
              , 2 ^ (sizeLow + 7)
              , 2 ^ (sizeLow + 8)
              , 2 ^ (sizeLow + 9)
              , 2 ^ (sizeLow + 10)
              ]
step        = sizeLow `div` 10
numSteps    = 10
randList n  = replicateM n randomRComplex
sizeLow     = 10

randomRComplex = do
  n1 <- randomRIO (0.0, 1.0 :: Float)
  n2 <- randomRIO (0.0, 1.0 :: Float)
  return $ n1 :+ n2

main = cmain -- msMain 100000

msMain sz = do
  l <- randList sz
  t'init <- getTime Realtime
  fftp l >>= ensure
  t'last <- getTime Realtime
  print $ t'last - t'init


config = defaultConfig
  { confInterval = cl99
  }

mkEnv = mapM randList range

cmain =
  defaultMainWith config
      [ env mkEnv mkMsBench
      , env mkEnv mkSqBench
      ]
  where
    mkMsBench l = bgroup "par" $ take (length range) $ go l
      where
        go ~(l:t) = bench (show $ length l) (nfIO $ fftp l) : go t
    mkSqBench l = bgroup "seq" $ take (length range) $ go l
      where
        go ~(l:t) = bench (show $ length l) (nf fft l) : go t
