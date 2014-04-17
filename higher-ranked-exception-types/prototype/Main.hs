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


exs  = [ex01,ex02,ex03,ex04,ex05,ex06,ex07,ex08,ex09,ex10
       ,ex11,ex12,ex13,ex14,ex15,ex16,ex17,ex18
       ]


-- * abstraction
ex01 = Abs 1 Bool $ Var 1
ex02 = Abs 1 Bool $ Abs 2 Bool $ Var 1
ex03 = Abs 1 Bool $ Abs 2 Bool $ Var 2
-- * application
ex04 = Abs 1 (Bool :-> Bool) $ Abs 2 Bool $ App (Var 1) (Var 2)
-- * crash
ex05 = Crash "foo" Bool
ex06 = Crash "foo" (Bool :-> Bool)
ex07 = App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool)
ex08 = App (Abs 1 Bool (Var 1)) (Crash "foo" Bool)
-- ex09: (bool,8,[e2 :<: 4,{foo} :<: 4,e5 :<: 6,{bar} :<: 6,(e3 e6) :<: 8,e4 :<: 8])
--       not that e3 is by default set to {}, so we lose e6 = {bar}. also see ex11.
ex09 = App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool)
ex10 = Abs 1 Bool $ App (Crash "foo" (Bool :-> Bool)) (Var 1)
-- ex11: the analysis does not seem the be sound w.r.t. imprecise exception
--       semantics for this example! i'm not sure if that can be resolved
--       without re-introducing non-emptyness guards, losing precision, or
--       collapsing to indistinguishable exceptions.
--       however: this might only affect applications and not conditionals
--       for which we need the imprecise semantics to allow for a case-
--       switching transformation.
--       intuitively/according to the analysis only "foo" can be raised here,
--       but the imprecise exception semantics would also allow for "bar".
ex11 = Abs 1 Bool $ App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool)
-- * seq
ex12 = Seq (Crash "foo" Bool) (Crash "bar" Bool)
ex13 = Seq (Crash "foo" (Bool :-> Bool)) (Abs 1 Bool $ Var 1)
ex14 = Abs 1 Bool $ Seq (Var 1) (Crash "foo" Bool)
ex15 = Abs 1 Bool $ Seq (Crash "foo" Bool) (Crash "bar" Bool)
ex16 = Abs 1 Bool $ Seq (Crash "bar" (Bool :-> Bool)) (Abs 2 Bool $ Var 2)
ex17 = Abs 1 Bool $ Seq (Var 1) (Abs 2 Bool $ Var 1)
-- * recursive functions
ex18 = (Abs 1 (Bool :-> Bool) (Abs 2 Bool (App (Var 1) (Var 2))))
-- * high-order functions
