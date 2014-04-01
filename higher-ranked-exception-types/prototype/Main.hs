module Main where

import           Names
import           Common      as C
import           Infer       as Inf
import qualified LambdaUnion as LU

{- LambdaUnion
env1 = [(0,C)]
e1   = Abs 1 (C :=> C) (App (Var 1) (Var 0))
e2   = App (Abs 2 C (Abs 1 (C:=>C) (App (Var 1) (Var 2)))) (App (Abs 3 C (Var 3)) (Var 0))
-} 

main   = mapM_ (putStrLn . show . run) exs
run ex = evalFresh (reconstruct [] [] ex) 1


exs  = [ex01,ex02,ex03,ex04]

-- abstraction
ex01 = Abs 1 Bool $ Var 1
ex02 = Abs 1 Bool $ Abs 2 Bool $ Var 1
ex03 = Abs 1 Bool $ Abs 2 Bool $ Var 2
-- application
ex04 = Abs 1 (Bool :-> Bool) $ Abs 2 Bool $ App (Var 1) (Var 2)

