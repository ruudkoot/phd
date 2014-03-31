module Main where

import qualified Common      as C
import qualified Infer       as Inf
import           LambdaUnion

env1 = [(0,C)]
e1   = Abs 1 (C :=> C) (App (Var 1) (Var 0))
e2   = App (Abs 2 C (Abs 1 (C:=>C) (App (Var 1) (Var 2)))) (App (Abs 3 C (Var 3)) (Var 0))

main = do
    putStrLn $ show (semanticallyEqual env1 e1 e2)
