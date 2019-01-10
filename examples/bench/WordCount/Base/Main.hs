{-# OPTIONS_GHC -threaded #-}
module Main where

import Control.Monad
import Control.DeepSeq
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import System.Random ( randomRIO )
import System.Clock

import Criterion.Main
import Criterion.Types

import Atoms
import WordCount

ensure :: NFData a => a -> IO a
ensure xs = xs `deepseq` return xs


range       = [ sizeLow
              , sizeLow + step 1
              , sizeLow + step 2
              , sizeLow + step 4
              , sizeLow + step 6
              , sizeLow + step 8
              , sizeLow + step 10
              ]
step     i  = sizeLow * i * 10
numSteps    = 10
randList n  = TIO.readFile "../input.txt" >>= ensure . Text.take n
sizeLow     = 10000
sizeHigh    = sizeLow

main = cmain

msMain sz = do
  l <- randList sz
  t'init <- getTime Realtime
  wordpar (spltw l) >>= ensure
  t'last <- getTime Realtime
  print $ t'last - t'init
  t'init <- getTime Realtime
  ensure $ wordc (spltw l)
  t'last <- getTime Realtime
  print $ t'last - t'init


config = defaultConfig {
            resamples = 10
         }

cmain = do
  lss <- mapM randList range >>= ensure
  defaultMainWith config
      [ bgroup "seq" $ map mkMsBench lss
      , bgroup "par" $ map mkParBench lss
      , bgroup "std" $ map mkBench lss
      ]
  where
    mkMsBench l = bench (show $ Text.length l) $ nf wordCount l
    mkParBench l = bench (show $ Text.length l) $ nfIO $ wordpar $ spltw l
    mkBench l = bench (show $ Text.length l) $ nf (count . spltw) l
