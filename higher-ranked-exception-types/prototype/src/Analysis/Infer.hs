module Analysis.Infer (
    module Analysis.Infer.Reconstruct,
    module Analysis.Infer.Print,
    inferenceExamples
) where

import Analysis.Common
import Analysis.Infer.Reconstruct
import Analysis.Infer.Print

inferenceExamples = map show [
    -- decent first example
    App (Abs 1 (Bool:->Bool) (Var 1)) (Abs 2 Bool (Var 2)),
    -- * constants
    Con True,
    -- * abstraction
    Abs 1 Bool $ Var 1,
    Abs 1 Bool $ Abs 2 Bool $ Var 1,
    Abs 1 Bool $ Abs 2 Bool $ Var 2,
    -- * application
    Abs 1 (Bool :-> Bool) $ Abs 2 Bool $ App (Var 1) (Var 2),
    -- * crash
    Crash "foo" Bool,
    Crash "foo" (Bool :-> Bool),
    App (Abs 1 Bool (Var 1)) (Crash "foo" Bool),
    -- ex09: (bool,8,[e2 :<: 4,{foo} :<: 4,e5 :<: 6,{bar} :<: 6,(e3 e6) :<: 8,e4 :<: 8])
    --       not that e3 is by default set to {}, so we lose e6 = {bar}. also see ex11.
    App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool),
    Abs 1 Bool $ App (Crash "foo" (Bool :-> Bool)) (Var 1),
    -- ex11: the analysis does not seem the be sound w.r.t. imprecise exception
    --       semantics for this example! i'm not sure if that can be resolved
    --       without re-introducing non-emptyness guards, losing precision, or
    --       collapsing to indistinguishable exceptions.
    --       however: this might only affect applications and not conditionals
    --       for which we need the imprecise semantics to allow for a case-
    --       switching transformation.
    --       intuitively/according to the analysis only "foo" can be raised here,
    --       but the imprecise exception semantics would also allow for "bar".
    Abs 1 Bool $ App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool),
    -- * seq
    Seq (Crash "foo" Bool) (Crash "bar" Bool),
    Seq (Crash "foo" (Bool :-> Bool)) (Abs 1 Bool $ Var 1),
    Abs 1 Bool $ Seq (Var 1) (Crash "foo" Bool),
    Abs 1 Bool $ Seq (Crash "foo" Bool) (Crash "bar" Bool),
    Abs 1 Bool $ Seq (Crash "bar" (Bool :-> Bool)) (Abs 2 Bool $ Var 2),
    Abs 1 Bool $ Seq (Var 1) (Abs 2 Bool $ Var 1),
    -- * recursive functions
    Fix (Abs 1 (Bool :-> Bool) (Abs 2 Bool (App (Var 1) (Var 2)))),
    -- * lists
    Nil Bool,
    Nil (Bool :-> Bool),
    Cons (Crash "foo" Bool) (Nil Bool),
    Cons (Abs 1 Bool (Var 1)) (Nil (Bool :-> Bool)),
    Cons (Abs 1 Bool (Crash "foo" Bool)) (Nil (Bool :-> Bool)),
    Cons (Abs 1 Bool (Var 1)) (Cons (Abs 1 Bool (Var 1)) (Nil (Bool :-> Bool))),
    Cons (Abs 1 Bool (Var 1)) (Cons (Abs 1 Bool (Crash "foo" Bool)) (Nil (Bool :-> Bool))),
    -- * non-recursive functions on lists
    Abs 1 (List Bool) (Case (Var 1) (Con True) 2 3 (Con False)),
    Abs 1 (List Bool) (Case (Var 1) (Crash "head" Bool) 2 3 (Var 2)),
    Abs 1 (List Bool) (Case (Var 1) (Crash "tail" (List Bool)) 2 3 (Var 3)),
    -- * recursive functions on lists
    ex29,
    Fix ex29,
    exMap,
    Fix exMap,
    exFilter,
    Fix exFilter,
    exRisers,
    Fix exRisers,
    exCrashOrDiverge1,
    exCrashOrDiverge2,
    exCrashOrDiverge3
    -- * high-order functions
  ] where
        ex29 = Abs 1 (List Bool :-> List Bool) $ Abs 2 (List Bool) $
                Case (Var 2) (Nil Bool) 3 4 (Cons (Var 3) (App (Var 1) (Var 4)))
        exMap = Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                    Case (Var 3) (Nil Bool) 4 5
                         (Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5)))
        exFilter =
            Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                    Case (Var 3) (Nil Bool) 4 5 $
                        If (App (Var 2) (Var 4))
                           (Cons (Var 4) (App (App (Var 1) (Var 2)) (Var 5)))
                           (App (App (Var 1) (Var 2)) (Var 5))
        exRisers =
            Abs 1 (List Int :-> List (List Int)) $ Abs 2 (List Int) $
                Case (Var 2) (Nil (List Int)) 3 4 $
                    Case (Var 4) (Cons (Cons (Var 3) (Nil Int)) (Nil (List Int))) 5 6 $
                        Case (App (Var 1) (Cons (Var 5) (Var 6)))
                             (Crash "risers" (List (List Int))) 7 8 $
                            If (BinOp (Var 3) (Var 5))
                               (Cons (Cons (Var 3) (Var 7)) (Var 8))
                               (Cons (Cons (Var 3) (Nil Int)) (Cons (Var 7) (Var 8)))
        exCrashOrDiverge1 =
            Abs 1 (List Int) $ Fix $ Abs 2 Bool $
                Case (Var 1) (Crash "diverge1" Bool) 3 4 (Var 2)
        exCrashOrDiverge2 =
            Abs 1 (List Int) $ Fix $ Abs 2 (Int :-> Int) $ Abs 3 Int $
                Case (Var 1) (Crash "diverge2" Int) 4 5 (App (Var 2) (Var 4))
        exCrashOrDiverge3 =
            Abs 1 (List Int) $ Fix $ Abs 2 (List Int :-> List Int) $ Abs 3 (List Int) $
                Case (Var 1) (Crash "diverge3" (List Int)) 4 5 $ 
                    Seq (Var 4) (App (Var 2) (Var 5))
