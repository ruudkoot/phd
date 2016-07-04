module Main where

import qualified Unif
import qualified Test

main = do
    Test.main
    putStrLn "\n\n"
    print Test.test_agUnifN_5
