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
    -- eta-conversion
    "eta1" # exEta1,
    "eta2" # exEta2,
    "eta3" # App exEta1 (Con True),
    "eta4" # App exEta2 (Con True),
    "eta5" # Seq exEta1 (Con True),
    "eta6" # Seq exEta2 (Con True),
    -- decent first examples
    "id id" # App (Abs 1 (Bool:->Bool) (Var 1)) (Abs 2 Bool (Var 2)),
    "" # Abs 1 (Bool :-> Bool) (App (Var 1) (Con True)),
    "" # Abs 1 Bool (Seq (Var 1) (Abs 2 Bool (Var 2))),
    "" # Seq (Crash "F" ((Bool :-> Bool) :-> Bool)) $ Abs 1 (Bool :-> Bool) $ If (Crash "G" Bool) (App (Var 1) (Con True)) (App (Var 1) (Crash "E" Bool)),
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
    "fix" # Fix (Abs 1 (Bool :-> Bool) (Abs 2 Bool (App (Var 1) (Var 2)))),
    "FIX" # FIX 1 (Bool :-> Bool) (Abs 2 Bool (App (Var 1) (Var 2))),

    -- * Dussart, Henglein & Mossin (soundness)
    -- fix (\f -> \x -> \y -> if x then True else f y x)
    -- METHOD 1: UNSOUND / METHOD 2: sound, 2 iterations
    "dhm" # Fix $ Abs 1 (Bool :-> (Bool :-> Bool)) $ Abs 2 Bool $ Abs 3 Bool $
                If (Var 2) (Con True) (App (App (Var 1) (Var 3)) (Var 2)),
    "DHM" # FIX 1 (Bool :-> (Bool :-> Bool)) $ Abs 2 Bool $ Abs 3 Bool $
                If (Var 2) (Con True) (App (App (Var 1) (Var 3)) (Var 2)),


    -- fix (\f -> \x -> \y -> \z -> If x then True else f z x y)
    -- METHOD 1: UNSOUND / METHOD 2: sound, 3 iterations
    "dhm3" # Fix $ Abs 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 2) (Con True) $
                        App (App (App (Var 1) (Var 4)) (Var 2)) (Var 3),
    "DHM3" # FIX 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 2) (Con True) $
                        App (App (App (Var 1) (Var 4)) (Var 2)) (Var 3),

    -- * Glenn, Stuckey & Sulzmann (precision)
    -- h x y b = if b then x else h x (h y x b) b
    -- fix (\h x y b -> if b then x else h x (h y x b) b
    -- note: 2nd parameter will not be forced
    "gss" # Fix $ Abs 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 4) (Var 2) $
                        App (App (App (Var 1) (Var 2)) (
                            App (App (App (Var 1) (Var 3)) (Var 2)) (Var 4)
                        )) (Var 4),
    "GSS" # FIX 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 4) (Var 2) $
                        App (App (App (Var 1) (Var 2)) (
                            App (App (App (Var 1) (Var 3)) (Var 2)) (Var 4)
                        )) (Var 4),

    -- h x y b = if b then x else h (h y x (not b)) x (not b)
    -- fix (\h x y b -> if b then x else h (h y x b) x b
    -- note: 'not' has been omitted, but should not influence static semantics
    -- note: 2nd parameter might be forced
    "gss'" # Fix $ Abs 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 4) (Var 2) $
                        App (App (App (Var 1) (
                            App (App (App (Var 1) (Var 3)) (Var 2)) (Var 4)
                        )) (Var 2)) (Var 4),
    "GSS'" # FIX 1 (Bool :-> (Bool :-> (Bool :-> Bool))) $
                Abs 2 Bool $ Abs 3 Bool $ Abs 4 Bool $
                    If (Var 4) (Var 2) $
                        App (App (App (Var 1) (
                            App (App (App (Var 1) (Var 3)) (Var 2)) (Var 4)
                        )) (Var 2)) (Var 4),
                            
    -- * Stefan's examples
    -- (fix (\f -> \x -> if y then f False else True)) True
    -- reinterpreted as: (fix (\f -> \x -> if x then f False else True)) True
    "stefan1'" # Fix $ Abs 1 (Bool :-> Bool) $ Abs 2 Bool $ 
                    If (Var 2) (App (Var 1) (Con False)) (Con True),
    "STEFAN1'" # FIX 1 (Bool :-> Bool) $ Abs 2 Bool $ 
                    If (Var 2) (App (Var 1) (Con False)) (Con True),
    "stefan1" # App (Fix $ Abs 1 (Bool :-> Bool) $ Abs 2 Bool $ 
                    If (Var 2) (App (Var 1) (Con False)) (Con True)) (Con True),
    "STEFAN1" # App (FIX 1 (Bool :-> Bool) $ Abs 2 Bool $ 
                    If (Var 2) (App (Var 1) (Con False)) (Con True)) (Con True),
    -- (fix (\f -> \x -> \y -> if x then True else f y x)) True False
    "stefan2" # App (App (Fix $ Abs 1 (Bool :-> (Bool :-> Bool)) $ Abs 2 Bool $ Abs 3 Bool $ If (Var 2) (Con True) (App (App (Var 1) (Var 3)) (Var 2))) (Con True)) (Con False),
    "STEFAN2" # App (App (FIX 1 (Bool :-> (Bool :-> Bool)) $ Abs 2 Bool $ Abs 3 Bool $ If (Var 2) (Con True) (App (App (Var 1) (Var 3)) (Var 2))) (Con True)) (Con False),

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
    "" # Abs       1 (List Bool :-> List Bool) $ ex29,
    "" # Fix $ Abs 1 (List Bool :-> List Bool) $ ex29,
    "" # FIX       1 (List Bool :-> List Bool) $ ex29,
    "" # Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap,
    "map" # Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap,
    "map id" # App (Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap) (Abs 6 Bool (Var 6)),
    "map (const E)" # App (Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap) (App (Abs 6 Bool (Abs 7 Bool (Var 6))) (Crash "E" Bool)),
    "MAP" # FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap,
    "MAP id" # App (FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap) (Abs 6 Bool (Var 6)),
    "MAP (const E)" # App (FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exMap) (App (Abs 6 Bool (Abs 7 Bool (Var 6))) (Crash "E" Bool)),
    -- * METHOD 1: sound(?) / METHOD 2: sound, 2 iterations
    "evilMap" # Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exEvilMap,
    "evilMap id" # App (Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exEvilMap) (Abs 8 Bool (Var 8)),
    "evilMap (const E)" # App (Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exEvilMap) (App (Abs 8 Bool (Abs 9 Bool (Var 8))) (Crash "E" Bool)),
    "EvilMap" # FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exEvilMap,
    "EvilMap id" # App (FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exEvilMap) (Abs 8 Bool (Var 8)),
    "EvilMap (const E)" # App (FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exEvilMap) (App (Abs 8 Bool (Abs 9 Bool (Var 8))) (Crash "E" Bool)),
    -- * METHOD 1: UNSOUND / METHOD 2: sound, 2 iterations
    "satanicMap" # Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exSatanicMap,
    "satanicMap id" # App (Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exSatanicMap) (Abs 8 Bool (Var 8)),
    "satanicMap (const E)" # App (Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exSatanicMap) (App (Abs 8 Bool (Abs 9 Bool (Var 8))) (Crash "E" Bool)),
    "SatanicMap" # FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exSatanicMap,
    "SatanicMap id" # App (FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exSatanicMap) (Abs 8 Bool (Var 8)),
    "SatanicMap (const E)" # App (FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exSatanicMap) (App (Abs 8 Bool (Abs 9 Bool (Var 8))) (Crash "E" Bool)),
    "" # Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exFilter,
    "filter" # Fix $ Abs 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exFilter,
    "FILTER" # FIX 1 ((Bool :-> Bool) :-> (List Bool :-> List Bool)) $ exFilter,
    "" # Abs 1 (List Int :-> List (List Int)) $ Abs 2 (List Int) $ exRisers,
    "risers" # Fix $ Abs 1 (List Int :-> List (List Int)) $ Abs 2 (List Int) $ exRisers,
    "RISERS" # FIX 1 (List Int :-> List (List Int)) $ Abs 2 (List Int) $ exRisers,
    "" # exCrashOrDiverge1,
    "" # exCRASHOrDiverge1,
    "" # exCrashOrDiverge2,
    "" # exCRASHOrDiverge2,
    "" # exCrashOrDiverge3,
    "" # exCRASHOrDiverge3,
    -- * higher-order functions & eta-reduction
    "apply" # exApply,
    "apply'" # exApply',       -- exception types are not invariant under eta-reduction!
    "happly" # exHApply,
    "happly apply" # App exHApply exApply,
    "compose" # exCompose,
    "hcompose" # exHCompose,     -- FIXME: should those EmptySets be there? (GONE NOW?)
    "hcompose'" # exHCompose',    -- FIXME: e14 and e17 have been eta-expanded. is this okay?
    "hcompose compose" # App exHCompose exCompose,
    "hcompose' compose" # App exHCompose' exCompose,
    -- * very high-order
    -- * crashing fixpoints
    "fixId"     # Fix $ Abs 1 Bool (Var 1),
    "FIXId"     # FIX 1 Bool (Var 1),
    "fixCrash1" # Fix $ Crash "foo" (Bool :-> Bool),
    "fixCrash2" # Fix $ Crash "foo" ((Bool :-> Bool) :-> (Bool :-> Bool)),
    "fixCrash3" # Fix $ If (Con True) (Abs 1 Bool $ Crash "foo" Bool) (Crash "bar" (Bool :-> Bool)),
    "fixIfIdCrash" # Abs 1 Bool $ If (Var 1) (Fix $ Abs 2 Bool (Var 2))
                                             (Fix $ Crash "foo" (Bool :-> Bool))
  ] where
        exEta1 = Abs 1 Bool (App exEta2 (Var 1))
        exEta2 = Crash "E" (Bool :-> Bool)
        ex29 =
            Abs 2 (List Bool) $
                Case (Var 2) (Nil Bool) 3 4 (Cons (Var 3) (App (Var 1) (Var 4)))
        exMap =
            Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                Case (Var 3) (Nil Bool) 4 5 $
                     Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5))
        exEvilMap =
            Seq (Crash "X" Bool) $
                Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                    Case (Var 3) (Nil Bool) 4 5 $
                         Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5))
        exSatanicMap =  -- Note the recursion in the guard of the inner case.
            Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                Case (Var 3) (Nil Bool) 4 5 $ Seq
                    (Case (App (App (Var 1) (Var 2)) (Var 5)) (Crash "A" Bool) 6 7 (Var 6))
                    (Cons (App (Var 2) (Var 4)) (App (App (Var 1) (Var 2)) (Var 5)))
        exFilter =
            Abs 2 (Bool :-> Bool) $ Abs 3 (List Bool) $
                Case (Var 3) (Nil Bool) 4 5 $
                    If (App (Var 2) (Var 4))
                       (Cons (Var 4) (App (App (Var 1) (Var 2)) (Var 5)))
                       (App (App (Var 1) (Var 2)) (Var 5))
        exRisers =
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
        exCRASHOrDiverge1 =
            Abs 1 (List Int) $ FIX 2 Bool $
                Case (Var 1) (Crash "diverge1" Bool) 3 4 (Var 2)
        exCRASHOrDiverge2 =
            Abs 1 (List Int) $ FIX 2 (Int :-> Int) $ Abs 3 Int $
                Case (Var 1) (Crash "diverge2" Int) 4 5 (App (Var 2) (Var 4))
        exCRASHOrDiverge3 =
            Abs 1 (List Int) $ FIX 2 (List Int :-> List Int) $ Abs 3 (List Int) $
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
