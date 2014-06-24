module Main where

import           Names
import           Common      as C
import           Infer       as Inf
import qualified LambdaUnion as LU
import           Latex

{- LambdaUnion
env1 = [(0,C)]
e1   = Abs 1 (C :=> C) (App (Var 1) (Var 0))
e2   = App (Abs 2 C (Abs 1 (C:=>C) (App (Var 1) (Var 2)))) (App (Abs 3 C (Var 3)) (Var 0))
-} 

-- | Main

main :: IO ()
main = do
    putStrLn $ unlines [
            "\\documentclass[fullpage]{article}",
            "\\usepackage[a4paper,landscape,margin=0pt]{geometry}",
            "%include polycode.fmt",
            "%include forall.fmt",
            "%include ../documentation/include/code.lhs2tex",
            "%include ../documentation/include/inference.lhs2tex",
            "%include ../documentation/definitions/lambda-union.lhs2tex",
            "%include ../documentation/definitions/completion.lhs2tex",
            "%include ../documentation/definitions/algorithm.lhs2tex",
            "\\begin{document}"
        ]
    mapM_ (putStrLn . run) exs
    putStrLn $ unlines [
            "\\end{document}"
        ]

run :: Expr -> String
run ex =
    let ((ty, e, cs, kenv), l) = runFreshLog (reconstruct [] [] ex) 1
     in unlines [
            "\\paragraph{Expression}",
            "...",
            "\\begin{code}",
            lhs2tex ex,
            "\\end{code}",
            "\\paragraph{Type}",
            "...",
            "\\begin{code}",
            lhs2tex ty,
            "\\end{code}",
            "\\paragraph{Algorithm}",
            "...",
            concatMap f l,
            "\\newpage"            
         ]
            where f x = unlines [x]

-- | Examples

exs  = [ex00
       ,ex01,ex02,ex03,ex04,ex05,ex06,ex07,ex08,ex09,ex10
       ,ex11,ex12,ex13,ex14,ex15,ex16,ex17,ex18,ex19,ex20
       ,ex21,ex22,ex23,ex24,ex25,ex26,ex27,ex28,ex29,ex30
       ]

-- * constants
ex00 = Con True
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
ex18 = Fix (Abs 1 (Bool :-> Bool) (Abs 2 Bool (App (Var 1) (Var 2))))
-- * lists
ex19 = Nil Bool
ex20 = Nil (Bool :-> Bool)
ex21 = Cons (Crash "foo" Bool) (Nil Bool)
ex22 = Cons (Abs 1 Bool (Var 1)) (Nil (Bool :-> Bool))
ex23 = Cons (Abs 1 Bool (Crash "foo" Bool)) (Nil (Bool :-> Bool))
ex24 = Cons (Abs 1 Bool (Var 1)) (Cons (Abs 1 Bool (Var 1)) (Nil (Bool :-> Bool)))
ex25 = Cons (Abs 1 Bool (Var 1)) (Cons (Abs 1 Bool (Crash "foo" Bool)) (Nil (Bool :-> Bool)))
-- * non-recursive functions on lists
ex26 = Abs 1 (List Bool) (Case (Var 1) (Con True) 2 3 (Con False))
ex27 = Abs 1 (List Bool) (Case (Var 1) (Crash "head" Bool) 2 3 (Var 2))
ex28 = Abs 1 (List Bool) (Case (Var 1) (Crash "tail" (List Bool)) 2 3 (Var 3))
-- * recursive functions on lists
ex29 = Abs 1 (List Bool :-> List Bool) $ Abs 2 (List Bool) $
        Case (Var 2) (Nil Bool) 3 4 (Cons (Var 3) (App (Var 1) (Var 4)))
ex30 = Fix ex29
ex31 = Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $
        Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
            Case (Var 3) (Nil Bool) 4 5
                 (Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5)))
ex32 = Fix ex29
-- * high-order functions
