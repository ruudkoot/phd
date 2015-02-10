module Analysis.Infer (
    module Analysis.Infer.Reconstruct,
    module Analysis.Infer.Print,
    inferenceExamples
) where

import Analysis.Common
import Analysis.Print
import Analysis.Infer.Reconstruct
import Analysis.Infer.Print

(#) :: a -> b -> (a, b)
x # y = (x, y)

infixr 0 #

inferenceExamples = map (\(l,x) -> (l, show x, mathjax' x)) [
    -- decent first example
    "id id" # App (Abs 1 (Bool:->Bool) (Var 1)) (Abs 2 Bool (Var 2)),
    -- * constants
    "true" # Con True,
    -- * abstraction
    "" # Abs 1 Bool $ Var 1,
    "" # Abs 1 Bool $ Abs 2 Bool $ Var 1,
    "" # Abs 1 Bool $ Abs 2 Bool $ Var 2,
    -- * application
    "" # Abs 1 (Bool :-> Bool) $ Abs 2 Bool $ App (Var 1) (Var 2),
    -- * crash
    "" # Crash "foo" Bool,
    "" # Crash "foo" (Bool :-> Bool),
    "" # Crash "foo" ((Bool :-> Bool) :-> Bool),
    "" # App (Abs 1 Bool (Var 1)) (Crash "foo" Bool),
    -- ex09: (bool,8,[e2 :<: 4,{foo} :<: 4,e5 :<: 6,{bar} :<: 6,(e3 e6) :<: 8,e4 :<: 8])
    --       not that e3 is by default set to {}, so we lose e6 = {bar}. also see ex11.
    "" # App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool),
    "" # Abs 1 Bool $ App (Crash "foo" (Bool :-> Bool)) (Var 1),
    -- ex11: the analysis is not sound w.r.t. imprecise exception semantics
    --       for this example! i'm not sure if that can be resolved
    --       without re-introducing non-emptyness guards, losing precision, or
    --       collapsing to indistinguishable exceptions.
    --       however: this might only affect applications and not conditionals
    --       for which we need the imprecise semantics to allow for a case-
    --       switching transformation.
    --       intuitively/according to the analysis only "foo" can be raised here,
    --       but the imprecise exception semantics would also allow for "bar".
    "" # Abs 1 Bool $ App (Crash "foo" (Bool :-> Bool)) (Crash "bar" Bool),
    -- * seq
    "" # Seq (Crash "foo" Bool) (Crash "bar" Bool),
    "" # Seq (Crash "foo" (Bool :-> Bool)) (Abs 1 Bool $ Var 1),
    "" # Abs 1 Bool $ Seq (Var 1) (Crash "foo" Bool),
    "" # Abs 1 Bool $ Seq (Crash "foo" Bool) (Crash "bar" Bool),
    "" # Abs 1 Bool $ Seq (Crash "bar" (Bool :-> Bool)) (Abs 2 Bool $ Var 2),
    "" # Abs 1 Bool $ Seq (Var 1) (Abs 2 Bool $ Var 1),
    -- * recursive functions
    "" # Fix (Abs 1 (Bool :-> Bool) (Abs 2 Bool (App (Var 1) (Var 2)))),
    -- * METHOD 1: UNSOUND / METHOD 2: sound, 2 iterations
    "dhm" # Fix $ Abs 1 (Bool :-> (Bool :-> Bool)) $ Abs 2 Bool $ Abs 3 Bool $
                If (Var 2) (Con True) (App (App (Var 1) (Var 3)) (Var 2)),
    -- * METHOD 1: UNSOUND / METHOD 2: sound, 3 iterations
    "dhm3" # Fix $ Abs 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 2) (Con True) $
                        App (App (App (Var 1) (Var 4)) (Var 2)) (Var 3),
    -- * lists
    "" # Nil Bool,
    "" # Nil (Bool :-> Bool),
    "" # Cons (Crash "foo" Bool) (Nil Bool),
    "" # Cons (Abs 1 Bool (Var 1)) (Nil (Bool :-> Bool)),
    "" # Cons (Abs 1 Bool (Crash "foo" Bool)) (Nil (Bool :-> Bool)),
    "" # Cons (Abs 1 Bool (Var 1)) (Cons (Abs 1 Bool (Var 1)) (Nil (Bool :-> Bool))),
    "" # Cons (Abs 1 Bool (Var 1)) (Cons (Abs 1 Bool (Crash "foo" Bool)) (Nil (Bool :-> Bool))),
    -- * non-recursive functions on lists
    "" # Abs 1 (List Bool) (Case (Var 1) (Con True) 2 3 (Con False)),
    "head" # Abs 1 (List Bool) (Case (Var 1) (Crash "head" Bool) 2 3 (Var 2)),
    "tail" # Abs 1 (List Bool) (Case (Var 1) (Crash "tail" (List Bool)) 2 3 (Var 3)),
    -- * recursive functions on lists
    "" # ex29,
    "" # Fix ex29,
    "" # exMap,
    "map" # Fix exMap,
    "map id" # App (Fix exMap) (Abs 6 Bool (Var 6)),
    "map (const E)" # App (Fix exMap) (App (Abs 6 Bool (Abs 7 Bool (Var 6))) (Crash "E" Bool)),
    -- * METHOD 1: sound / METHOD 2: sound, 2 iterations
    "evilMap" # Fix exEvilMap,
    "evilMap id" # App (Fix exEvilMap) (Abs 8 Bool (Var 8)),
    "evilMap (const E)" # App (Fix exEvilMap) (App (Abs 8 Bool (Abs 9 Bool (Var 8))) (Crash "E" Bool)),
    -- * METHOD 1: UNSOUND / METHOD 2: sound, 2 iterations
    "satanicMap" # Fix exSatanicMap,
    "satanicMap id" # App (Fix exSatanicMap) (Abs 8 Bool (Var 8)),
    "satanicMap (const E)" # App (Fix exSatanicMap) (App (Abs 8 Bool (Abs 9 Bool (Var 8))) (Crash "E" Bool)),
    "" # exFilter,
    "filter" # Fix exFilter,
    "" # exRisers,
    "risers" # Fix exRisers,
    "" # exCrashOrDiverge1,
    "" # exCrashOrDiverge2,
    "" # exCrashOrDiverge3,
    -- * higher-order functions & eta-reduction
    "apply" # exApply,
    "apply'" # exApply',       -- exception types are not invariant under eta-reduction!
    "happly" # exHApply,
    "happly apply" # App exHApply exApply,
    "compose" # exCompose,
    "hcompose" # exHCompose,     -- FIXME: should those EmptySets be there? (GONE NOW?)
    "hcompose'" # exHCompose',    -- FIXME: e14 and e17 have been eta-expanded. is this okay?
    "hcompose compose" # App exHCompose exCompose,
    "hcompose' compose" # App exHCompose' exCompose
    -- * very high-order
  ] where
        ex29 =
            Abs 1 (List Bool :-> List Bool) $ Abs 2 (List Bool) $
                Case (Var 2) (Nil Bool) 3 4 (Cons (Var 3) (App (Var 1) (Var 4)))
        exMap =
            Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                    Case (Var 3) (Nil Bool) 4 5 $
                         Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5))
        exEvilMap =
            Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $
                Seq (Crash "X" Bool) $
                    Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                        Case (Var 3) (Nil Bool) 4 5 $
                             Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5))
        exSatanicMap =  -- Note the recursion in the guard of the inner case.
            Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                    Case (Var 3) (Nil Bool) 4 5 $ Seq
                        (Case (App (App (Var 1) (Var 2)) (Var 5)) (Crash "A" Bool) 6 7 (Var 6))
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
        exApply =
            Abs 4 (Bool :-> Bool) $ Abs 5 Bool $ App (Var 4) (Var 5)
        exApply' =
            Abs 4 (Bool :-> Bool) $ Var 4
        exHApply =
            Abs 1 ((Bool :-> Bool) :-> (Bool :-> Bool)) $
                Abs 2 (Bool :-> Bool) $ Abs 3 Bool $ App (App (Var 1) (Var 2)) (Var 3)
        exCompose =
            Abs 5 (Bool :-> Bool) $ Abs 6 (Bool :-> Bool) $ Abs 7 Bool $
                App (Var 5) (App (Var 6) (Var 7))
        exHCompose =
            Abs 1 ((Bool :-> Bool) :-> ((Bool :-> Bool) :-> (Bool :-> Bool))) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (Bool :-> Bool) $
                    App (App (Var 1) (Var 2)) (Var 3)
        exHCompose' =
            Abs 1 ((Bool :-> Bool) :-> ((Bool :-> Bool) :-> (Bool :-> Bool))) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (Bool :-> Bool) $ Abs 4 Bool $
                    App (App (App (Var 1) (Var 2)) (Var 3)) (Var 4)
