module Main (main) where

import System.IO

import Control.Monad.State

import qualified Data.Map      as M
import qualified Data.Set      as S
import qualified Data.Set.Util as S
import qualified Data.Tree     as T

import           Common
import qualified Sem
import qualified Analysis as A
import qualified Constr   as C

-- | Main

main :: IO ()
main
    = do -- Preamble
         putStrLn $ preamble

         mapM_ testcase [ exV1,  exV2,  exV3,  exV4,  exV5,  exV6
                        , ex1 ,  ex2 ,  ex3 ,  ex4 ,  ex5 ,  ex6 ,  ex7 ,  ex8
                        , ex9 ,  ex10,  ex11,  ex12,  ex13,  ex14,  ex15,  ex16
                        , ex17  -- interesting example
                        , exT1,  exT2,  exT3,  exT4,  exT5
                        , exL1,  exL2,  exL3,  exL4,  exL5,  exL6,  exL7
                        , exC1,  exC2,  exC3,  exC4,  exC5,  exC6,  exC7,  exC8
                        , exC9,  exC10, exC11, exC12, exC13, exC14, exC15
                        , exF1,  exF2,  exF3,  exF4,  exF5,  exF6,  exF7,  exF8
                        , exQ1, exQ2
                        , exCS0, exCS1
                        , exR0, exR0a, exR0b
                        , exR1  -- interesting example
                        , exR1Nil
                        , exLength, exLengthApp, exLengthBroken, exLengthBrokenApp
                        , exRminimal, exRminimal0, exRminimal1, exRminimal2
                        ]

         -- Postamble
         putStrLn $ postamble

testcase :: Expr -> IO ()
testcase example
    = do putStrLn $ newpage
    
         -- * Expression
         putStrLn $ section "Expression"
         putStrLn $ gather example

         -- * Evaluation
         putStrLn $ section "Evaluation"

         let e' = evalState (Sem.transform example)
                            (map (augment "\\zeta") freshIdents)

         -- putStrLn $ subsection "Normal form"
         -- putStrLn $ gather e'

         putStrLn $ subsection "Reduction (WHNF)"
         let (_heap, z) = evalState (Sem.reduce 10000 M.empty e')
                                   (map (augment "\\xi") freshIdents)
         -- putStrLn $ gather heap
         putStrLn $ gather z

         putStrLn $ subsection "Reduction (further)"
         let (_heap', z') = evalState (Sem.reduceFurther 10000 M.empty e')
                                     (map (augment "\\xi") freshIdents)
         -- putStrLn $ gather heap'
         putStrLn $ gather z'

         putStrLn $ subsection "Post-processing"
         let ev@(evRef, evExn)     = postProcessEval  z
         putStrLn $ gather ev
         let ev2@(eevRef2, evExn2) = postProcessEval2 z'
         putStrLn $ gather ev2

         -- * Combined analysis
         
         putStrLn $ section "Underlying Types"
         
         let initC = freshIdents

         let ((sT, tT, eT'), initC') = runState (A.inferTy M.empty example) initC
         
         putStrLn $ subsection "Conclusion"
         putStrLn $ gather (sT A.$! tT)
         
         putStrLn $ subsection "Type Annotated Expression"
         putStrLn $ gather (sT A.$! eT')
         
         putStrLn $ section "Combined Analysis"

         let ((sC, tC, refC, rcC, exnC, ecC, vrfC, vcC, dC, dC', eC'), initC'')
                = runState (A.infer M.empty (sT A.$! eT')) initC'

         putStrLn $ subsection "Derivation Tree"
         putStrLn $ gather (sC A.$@ dC)
         mapM (\d' -> putStrLn $ gather (sC A.$@ d')) dC'

         putStrLn $ subsubsection "Conclusion"
         putStrLn $ gather (latex (sC A.$@ tC) ++ "\\ \\&\\ " ++ latex (sC A.$@ refC) ++ "; " ++ latex (sC A.$@ exnC) ++ "; " ++ latex (sC A.$@ vrfC))

         putStrLn $ subsubsection "Environment"
         putStrLn $ gather (A.extrEnv (sC A.$@ dC))

         -- putStrLn $ subsubsection "Substitution"
         -- putStrLn $ gather sC

         putStrLn $ subsubsection "Constraints"
         putStrLn $ gather (sC A.$@ rcC)
         putStrLn $ gather (sC A.$@ ecC)
         putStrLn $ gather (sC A.$@ vcC)

         putStrLn $ subsection "Solution of Data-Flow Constraints"
         let initSol1 = A.initSubst tC rcC (sC A.$@ eC') -- FIXME: also Exn and Vrf...
         let sol1 = C.solve rcC initSol1    -- FIXME: why no apply substitution to c1?
         let sol1' = (sol1, M.empty, M.empty)
         putStrLn $ gather sol1
         
         putStrLn $ subsection "Solution of Exception Constraints"
         let initSol2 = A.exnInitSubst tC ecC (sC A.$@ eC') -- FIXME: also Ref and Vrf...
         let sol2 = C.solve ecC initSol2    -- FIXME: why no apply substitution to c1?
         let sol2' = (M.empty, sol2, M.empty)
         putStrLn $ gather sol2
         
         putStrLn $ subsection "Solution of Verification Constraints"
         let initSol3 = A.vrfInitSubst tC vcC (sC A.$@ eC') -- FIXME: also Ref and Exn
         let sol3 = C.solve vcC initSol3    -- FIXME: why no apply substitution to c1?
         let sol3' = (M.empty, M.empty, sol3)
         putStrLn $ gather sol3
         
         putStrLn $ subsection "``Solved'' Derivation Tree" -- FIXME: FPI not yet done
         let sol' = (sol1, sol2, sol3)
         let dCsol = sol' A.$# (sC A.$@ dC)
         putStrLn $ gather dCsol
         putStrLn $ subsubsection "Conclusion"
         putStrLn $ gather (latex (sol' A.$# (sC A.$@ tC))
                            ++ "\\ \\&\\ " ++ latex (sol' A.$# (sC A.$@ refC))
                            ++ "; " ++ latex (sol' A.$# (sC A.$@ exnC))
                            ++ "; " ++ latex (sol' A.$# (sC A.$@ vrfC)) )
         putStrLn $ subsubsection "Collected"
         let exnCol = collectExn (sol2' A.$# (sC A.$@ tC)) (sol2' A.$# (sC A.$@ exnC))
         putStrLn $ gather exnCol
         let vrfCol = collectVrf (sol3' A.$# (sC A.$@ tC)) (sol3' A.$# (sC A.$@ vrfC))
         putStrLn $ gather vrfCol
         -- putStrLn $ subsubsection "Environment"
         -- putStrLn $ gather (A.extrEnv dCsol)

         -- Fix point iteration of exceptions and verification
         putStrLn $ section "Second-stage solver"
         putStrLn $ subsection "Step A"
         let solved2a = solve2a sol1 vrfCol
         putStrLn $ gather solved2a

         putStrLn $ subsection "Step B"
         let ctotal = ecC `S.union` solved2a
         putStrLn $ subsubsection "ctotal"
         putStrLn $ gather ctotal
         putStrLn $ subsubsection "decompose ctotal"
         putStrLn $ gather (C.decompose $ ctotal)
         putStrLn $ subsubsection "decompose + remove reflexive ctotal"
         putStrLn $ gather (C.removeReflexive . C.decompose $ ctotal)
         putStrLn $ subsubsection "xx-c2"
         let (xx_c2, xx_ns2)
                = C.contractCycles . C.removeReflexive . C.decompose $ ctotal
         let xx_s2 = A.Subst M.empty xx_ns2
         putStrLn $ gather xx_c2
         putStrLn $ gather (xx_s2 A.$@ xx_c2)
         putStrLn $ subsubsection "xx-c3"
         let xx_c3 = C.removeReflexive (xx_s2 A.$@ xx_c2)
         putStrLn $ gather xx_c3
         let solved2b = C.solve xx_c3 initSol2    -- FIXME: need to recalc initSol2
                -- FIXME: why no apply substitution to c2?
         let solved2b' = (sol1, solved2b, M.empty)
         putStrLn $ gather solved2b
         putStrLn $ gather (solved2b' A.$# (xx_s2 A.$@ sC A.$@ ctotal))
         putStrLn $ subsection "Results"
         let stage2sol = solved2b' A.$# (xx_s2 A.$@ sC A.$@ dC)
         -- putStrLn $ gather stage2sol
         putStrLn $ subsubsection "Conclusion"
         putStrLn $ gather (latex (solved2b' A.$# (xx_s2 A.$@ sC A.$@ tC)) ++ "\\ \\&\\ " ++ latex (solved2b' A.$# (xx_s2 A.$@ sC A.$@ exnC)))
         putStrLn $ subsubsection "Collected"
         putStrLn $ gather (collectExn (solved2b' A.$# (xx_s2 A.$@ sC A.$@ tC)) (solved2b' A.$# (xx_s2 A.$@ sC A.$@ exnC)))
         putStrLn $ subsubsection "Environment"
         putStrLn $ gather (A.extrEnv stage2sol)
         putStrLn $ subsubsection "Solved Verification Conditions"
         putStrLn $ gather (solSubst2 sol1 solved2b xx_s2 sol3)

         -- Testing
         hPutStrLn stderr (take 80 $ show example)

         putStrLn $ section "Testing"
         let anaRef = sol1' A.$# refC
         let C.Conc anaRef' = anaRef
         let C.Conc evRef'  = evRef
         
         putStrLn $ subsection "Types"
         putStrLn $ gather (maybeColor (if tT `A.alphaEquiv` A.underlyingType tC
                                        then Just "OliveGreen"
                                        else error ("underlying types: tT = " ++ show tT ++ ", tC = " ++ show tC ++ ", example = " ++ show example ++ ", eT' = " ++ show eT')
                                             Just "Red"
                                       )
                                     (latex tT ++ "\\equiv " ++ latex tC))

         putStrLn $ subsection "Dataflow"
         putStrLn $ gather (maybeColor (if evRef' `S.isSubsetOf` anaRef'
                                        then Just "OliveGreen"
                                        else error "dataflow analysis did not pass testing"
                                             Just "Red"
                                       )
                                     (latex evRef ++ "\\subseteq " ++ latex anaRef))

         putStrLn $ subsection "WHNF"
         let anaExn = sol2' A.$# exnC
         let fpiExn = solved2b' A.$# (xx_s2 A.$@ exnC)
         let C.Conc anaExn' = anaExn
         let C.Conc evExn'  = evExn
         let C.Conc fpiExn' = fpiExn
         putStrLn $ gather (maybeColor (if evExn' `S.isSubsetOf` fpiExn'
                                        then Just "OliveGreen"
                                        else error "fix-point iteration did not pass testing"
                                             Just "Red"
                                        )
                           (latex evExn ++ "\\subseteq " ++ latex fpiExn))

         putStrLn $ subsection "Further"
         let anaExn2 = collectExn (sol2' A.$# tC) (sol2' A.$# exnC)
         let fpiExn2 = collectExn (solved2b' A.$# (xx_s2 A.$@ tC)) (solved2b' A.$# (xx_s2 A.$@ exnC))
         let C.Conc anaExn2' = anaExn2
         let C.Conc fpiExn2' = fpiExn2
         let C.Conc evExn2'  = evExn2
         putStrLn $ gather (maybeColor (if evExn2' `S.isSubsetOf` fpiExn2'
                                        then Just "OliveGreen"
                                        else error "fix-point iteration did not pass testing"
                                             Just "Red"
                                        )
                           (latex evExn2 ++ "\\subseteq " ++ latex fpiExn2))

-- | Second-stage solver

-- * Use data-flow to propagate exceptions

-- FIXME: some extremely annoying type casts going on here...

solve2a :: A.RefSubst -> A.Vrf -> A.ExnConstr
solve2a refSol (C.Conc vrfs) = S.unionMap solve2a' vrfs where
    solve2a' :: A.Vrf' -> A.ExnConstr -- FIXME: Exn.Exn
    solve2a' (A.VrfCon _ (C.Unif ref) xpm exn)
        = let posPats :: S.Set A.Ref'
              C.Conc posPats = M.findWithDefault (error $ "solve2a: ref = " ++ show ref ++ ", refSol = " ++ show refSol) ref refSol -- refSol M.! ref
           in S.foldr (\b r -> S.insert ((A.injExn (xpm M.! b)) C.:<: exn) r) S.empty posPats

-- | Post-processing

-- * Dataflow and exceptions (up to WHNF) of the evaluation result

postProcessEval :: Expr -> (A.Ref, A.Exn)
postProcessEval (Con (ExnC lbl Crash           ))
    = ( C.Conc S.empty
      , C.Conc (S.singleton (A.ExnCrash lbl))       )
postProcessEval (Con (ExnC _lbl Diverge         ))
    = ( C.Conc S.empty
      , C.Conc S.empty                                )
postProcessEval (Con (ExnC lbl PatternMatchFail))
    = ( C.Conc S.empty
      , C.Conc (S.singleton (A.ExnCrash lbl))       ) -- FIXME: add separate exception
postProcessEval (Con (Bool b))
    = ( C.Conc (S.singleton (A.RefBool           b ))
      , C.Conc S.empty                                )
postProcessEval (Con (Int  n))
    = ( C.Conc (S.singleton (A.RefInt (A.injInt n)))
      , C.Conc S.empty                                )
postProcessEval (Abs _ _)
    = ( C.Conc S.empty
      , C.Conc S.empty                                )
-- Pairs
postProcessEval (Pair _ _)
    = ( C.Conc S.empty
      , C.Conc S.empty                                )
-- Lists
postProcessEval Nil
    = ( C.Conc (S.singleton (A.RefList A.E))
      , C.Conc S.empty                                )
postProcessEval (Cons _ _)
    = ( C.Conc (S.singleton (A.RefList A.NE))
      , C.Conc S.empty                                )
postProcessEval x
    = error $ "postProcessEval: " ++ show x

-- * Dataflow and exceptions (further) of the evaluation result

postProcessEval2 :: Expr -> (A.Ref, A.Exn)
    -- eval under constructors (not abstractions)
postProcessEval2 (Con (ExnC lbl Crash           ))
    = ( C.Conc S.empty
      , C.Conc (S.singleton (A.ExnCrash lbl))       )
postProcessEval2 (Con (ExnC _lbl Diverge         ))
    = ( C.Conc S.empty
      , C.Conc S.empty                                )
postProcessEval2 (Con (ExnC lbl PatternMatchFail))
    = ( C.Conc S.empty
      , C.Conc (S.singleton (A.ExnCrash lbl))       ) -- FIXME: add separate exception
postProcessEval2 (Con (Bool b))
    = ( C.Conc (S.singleton (A.RefBool           b ))
      , C.Conc S.empty                                )
postProcessEval2 (Con (Int  n))
    = ( C.Conc (S.singleton (A.RefInt (A.injInt n)))
      , C.Conc S.empty                                )
postProcessEval2 (Abs _ _)
    = ( C.Conc S.empty
      , C.Conc S.empty                                )
-- Pairs
postProcessEval2 (Pair e1 e2)
    = let (_, C.Conc exn1) = postProcessEval2 e1
          (_, C.Conc exn2) = postProcessEval2 e2
       in ( C.Conc S.empty
          , C.Conc (exn1 `S.union` exn2)              )
-- Lists
postProcessEval2 Nil
    = ( C.Conc (S.singleton (A.RefList A.E))
      , C.Conc S.empty                                )
postProcessEval2 (Cons e1 e2)
    = let (_, C.Conc exn1) = postProcessEval2 e1
          (_, C.Conc exn2) = postProcessEval2 e2
       in ( C.Conc (S.singleton (A.RefList A.NE))
          , C.Conc (exn1 `S.union` exn2)              )
postProcessEval2 x
    = error $ "postProcessEval2: " ++ show x

-- * Collect exceptions from inside constructors (but not abstractions)

collectExn :: A.Ty -> A.Exn -> A.Exn      -- FIXME: Seems more at home in Exn
                                          -- if it wasn't just for debugging
collectExn ty (C.Conc exn) = C.Conc (collectExn' ty `S.union` exn) where
    collectExn' (A.TyVar  _)
        = S.empty
    collectExn' (A.TyCon  _)
        = S.empty
    collectExn' (A.TyFun  _ _ _ _)
        = S.empty
    collectExn' (A.TyPair t1 (_, C.Conc exn1, _) t2 (_, C.Conc exn2, _))
        = collectExn' t1 `S.union` collectExn' t2 `S.union` exn1 `S.union` exn2
    collectExn' (A.TyList t (_, C.Conc exn, _))
        = collectExn' t `S.union` exn
        
collectVrf :: A.Ty -> A.Vrf -> A.Vrf
collectVrf ty vrf
    | C.Conc vrf' <- vrf
        = C.Conc (collectVrf' ty `S.union` vrf')
    | C.Unif vrf' <- vrf
        = C.Conc (collectVrf' ty `S.union` S.singleton (A.VrfVar vrf'))
  where
    collectVrf' (A.TyVar _)
        = S.empty
    collectVrf' (A.TyCon _)
        = S.empty
    collectVrf' (A.TyFun _ _ _ _)
        = S.empty
    collectVrf' (A.TyPair t1 (_, _, C.Conc vrf1) t2 (_, _, C.Conc vrf2))
        = collectVrf' t1 `S.union` collectVrf' t2 `S.union` vrf1 `S.union` vrf2
    collectVrf' (A.TyList t (_, _, C.Conc vrf))
        = collectVrf' t `S.union` vrf
    -- Collection from unsolved things
    collectVrf' (A.TyPair t1 (_, _, C.Unif vrf1) t2 (_, _, C.Unif vrf2))
        = collectVrf' t1 `S.union` collectVrf' t2
          `S.union` S.singleton (A.VrfVar vrf1)
          `S.union` S.singleton (A.VrfVar vrf2)
    collectVrf' (A.TyList t (_, _, C.Unif vrf))
        = collectVrf' t `S.union` S.singleton (A.VrfVar vrf)
        
-- * Substitutions for debugging purposes only (copied here from Verif)

solSubst2 :: A.RefSubst -> A.ExnSubst -> A.Subst -> A.VrfSubst -> A.VrfSubst
solSubst2 refSubst' exnSubst' exnSubst2   -- FIXME: awkward naming
                                          -- FIXME: do we still need exnSubst2?
    = M.map solSubst1 where
        refSubst = (refSubst', M.empty  , M.empty)
        exnSubst = (M.empty  , exnSubst', M.empty)
        solSubst1 (C.Conc vrfs)
            = C.Conc (S.map solSubst2 vrfs)
        solSubst2 (A.VrfCon lbl ref xpm exn)
            = A.VrfCon lbl
                (refSubst A.$# ref)
                (M.map solSubst3 xpm) 
                (exnSubst A.$# (exnSubst2 A.$@ exn))
        solSubst3 exn
            = exnSubst A.$# (exnSubst2 A.$@ exn)

-- | Examples

crash, crash1, crash2 :: Expr
crash  = Con $ ExnC "crash" Crash
crash1 = Con $ ExnC "1" Crash
crash2 = Con $ ExnC "2" Crash

ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9,
    ex10, ex11, ex12, ex13, ex14, ex15, ex16, ex17 :: Expr
ex1 = Let _const (Abs _k (Abs _x (Var _k))) (App (App (Var _const) (Con (Int 3))) (Con (Bool False)))
ex2 = Let _const (Abs _k (Abs _x (Var _k))) (App (App (Var _const) (Con (Bool True))) crash)
ex3 = Let _const (Abs _k (Abs _x (Var _k))) (Var _const)
ex4 = (App crash crash)
ex5 = (App crash (Con (Bool True)))
ex6 = Let _const (Abs _k (Abs _x (Var _k))) (App (Var _const) crash)
ex7 = Let _const (Abs _k (Abs _x (Var _k))) (App (App (Var _const) crash) (Con (Bool True)))
ex8 = Let _const (Abs _k (Abs _x (Var _k))) (App (App (Var _const) (Con (Bool True))) crash)
ex9 = Let (name "suspendedcrash") (Abs _x crash) (Var (name "suspendedcrash"))
ex10 = Let (name "suspendedcrash") (Abs _x crash) (App (Var (name "suspendedcrash")) (Con (Bool True)))
ex11 = If "if" crash (Con (Bool True)) (Con (Bool False))
ex12 = If "if" (Con (Bool True)) (Con (Bool False)) crash
ex13 = If "if" (Con (Bool True)) crash (Con (Bool True))
ex14 = Abs _x (If "if" (Var _x) crash (Con (Bool True)))
ex15 = App (Abs _x (If "if" (Var _x) crash1 (Con (Bool True)))) crash2
ex16 = App (Abs _x (If "if" (Var _x) crash (Con (Bool False)))) (Con (Bool True))
ex17 = App (Abs _x (If "if" (Var _x) crash (Con (Bool True)))) (Con (Bool False))

-- * Pairs / tuples
exT1, exT2, exT3, exT4, exT5 :: Expr
exT1 = Pair (Con $ Int 42) (Con $ Bool False)
exT2 = Pair (Con $ Int 42) (Con $ ExnC "exT2" Crash)
exT3 = Fst exT1
exT4 = Snd exT2
exT5 = Fst (Con $ ExnC "exT5" Crash)

-- * Lists
exL1, exL2, exL3, exL4, exL5, exL6, exL7 :: Expr
exL1 = Nil
exL2 = Cons (Con $ Bool True) Nil
exL3 = Cons (If "if" (Con $ Bool True) (Con $ Bool False) (Con $ Bool True)) Nil
exL4 = Abs _x (Cons (If "if" (Var _x) (Con $ Bool False) (Con $ Bool True)) Nil)
exL5 = Abs _x (Cons (If "if" (Var _x) (Var _x) (Con $ Bool True)) Nil)
exL6 = Abs _x (Cons (If "if" (Var _x) crash (Con $ Bool True)) Nil)
exL7 = Abs _x (Cons (If "if" (Var _x) (Var _x) (Con $ Bool True)) crash)

-- * Case-statements
exC1, exC2, exC3, exC4, exC5, exC6, exC7, exC8,
    exC9, exC10, exC11, exC12, exC13, exC14, exC15 :: Expr
exC1 = Case "case" Nil (Just (Con $ Bool True)) (Just (_x, _xs, Con $ Bool False))
exC2 = Abs _x (Case "case" (Var _x) (Just (Con $ Int 42)) (Just (_a, _as, App (Var _a) (Con $ Bool True))))
exC3 = Case "case" Nil (Just (Abs _x (Con $ Bool False))) (Just (_a, _as, If "if" (App (Var _a) (Con $ Bool True)) (Var _a) (Var _a)))
exC4 = Case "case" Nil (Just (Abs _x (Var _x))) (Just (_a, _as, If "if" (App (Var _a) (Con $ Bool True)) (Var _a) (Var _a)))
exC5 = Case "case" crash (Just (Abs _x (Var _x))) (Just (_a, _as, If "if" (App (Var _a) (Con $ Bool True)) (Var _a) (Var _a)))
exC6 = Case "case" Nil
            (Just crash)
            (Just (_a, _as, If "if" (App (Var _a) (Con $ Bool True)) (Var _a) (Var _a)))
exC7 = Case "case" Nil
            (Just (Abs _x (Var _x)))
            (Just (_a, _as, crash))
exC8 = Case "case" Nil
            (Just (Abs _x (Var _x)))
            (Just (_a, _as, If "if" (App (Var _a) crash) (Var _a) (Var _a)))
exC9 = Case "case" Nil
            (Just (Abs _x (Var _x)))
            (Just (_a, _as, If "if" crash (Var _a) (Var _a)))
exC10 = Case "case" Nil
             (Just (Abs _x (Var _x)))
             (Just (_a, _as, If "if" (App (Var _a) (Con $ Bool True))
                                  crash
                                  (Var _a)))
exC11 = Case "case" (Cons (Con $ Int 42) Nil)
             (Just crash)
             (Just (_x, _xs, crash))
exC12 = Case "case" (Cons (Con $ Int 42) Nil)
             (Just (Con $ Bool True))
             (Just (_x, _xs, Con $ Bool False))
exC13 = Case "case" (Cons (Con $ Int 42) Nil)
             (Just (Con $ Int (-13)))
             (Just (_x, _xs, Var _x))
exC14 = Case "case" (Cons (Con $ Int 42) (Cons (Con $ Int 666) Nil))
             (Just (Con $ Int (-13)))
             (Just (_x, _xs, Var _x))
exC15 = Case "case" (Cons (Con $ Int 42) (Cons (Con $ Int 666) Nil))
             (Just Nil)
             (Just (_x, _xs, Var _xs))

-- These should fail with _a unification error (constructor clash)
_exCerr1, _exCerr2 :: Expr
_exCerr1 = Case "case" (Con $ Bool True) (Just (Con $ Bool True)) (Just (_x, _xs, Con $ Bool False))
_exCerr2 = Case "case" Nil (Just (Con $ Bool True)) (Just (_x, _xs, Con $ Int 42))

-- * Fix points
exF1, exF2, exF3, exF4, exF5, exF6, exF7, exF8 :: Expr
exF1 = Fix _f crash
exF2 = App (Fix _f crash) crash
exF3 = Fix _f (Abs _x (App (Var _f) (Var _x)))
exF4 = App (Fix _f (Abs _x (App (Var _f) (Var _x)))) crash
exF5 = Fix _f (Abs _x (If "if" (Var _x) (Var _x) (Var _x)))
exF6 = App (Fix _f (Abs _x (If "if" (Var _x) (Var _x) (Var _x)))) crash
exF7 = Fix _f (Abs _x (If "if" (Var _x) (App (Var _f) (Var _x)) (App (Var _f) (Var _x))))
exF8 = App (Fix _f (Abs _x (If "if" (Var _x) (App (Var _f) (Var _x)) (App (Var _f) (Var _x))))) crash

-- * Need let-polymorphism

exP :: Expr
exP = Let _id (Abs _x (Var _x)) (App (Var _id) (Var _id))

-- * Recursion and pattern-matching

exQ1, exQ2 :: Expr
exQ1 = Fix _f (Abs _x (Case "case" (Var _x) (Just (Con $ Int 42)) (Just (_a,_as,App (Var _f) (Var _as)))))
exQ2 = App (Fix _f (Abs _x (Case "case" (Var _x) (Just (Con $ Int 42)) (Just (_a,_as,App (Var _f) (Var _as)))))) (Cons (Con $ Int 1) (Cons (Con $ Int 2) (Cons (Con $ Int 3) (Nil))))

-- * Abstraction and application of verification conditions

exV1, exV2, exV3, exV4, exV5, exV6 :: Expr
exV1 = Case "case" (Cons (Con $ Int 42) Nil) (Just (Con $ Bool True)) (Nothing)
exV2 = Abs _x exV1
exV3 = App exV2 (Con $ Int 13)
exV4 = Abs _x (Pair (Case "case" (Var _x) (Just (Var _x)) (Nothing))
                    (Con $ Int 13)) 
exV5 = Abs _x (Pair (Con $ Int 42)
                    (Case "case" (Var _x) (Nothing) (Just (_y, _ys, (Var _ys))))) 
exV6 = Abs _x (Pair (Case "case" (Var _x) (Just (Var _x)) (Nothing))
                    (Case "case" (Var _x) (Nothing) (Just (_y, _ys, (Var _ys))))) 

-- * Context-sensitivity

exCS0, exCS1 :: Expr
exCS0 = Abs _x
            (Case "a"
             (Var _x)
             (Just (Case "b"
                         (Var _x)
                         (Just (Con $ Int 1))
                         (Nothing)))
             (Just (_z,_zs,Con $ Int 2)))
exCS1 = App exCS0 Nil


-- * "Realistic" test-cases

exR0, exR0a, exR0b, exR1, exR1Nil, exRminimal, exRminimal0, exRminimal1,
    exRminimal2 :: Expr

-- risers
{- Mitchell:
risers :: Ord a => [a] -> [[a]]
risers [ ] = [ ]
risers [x] = [[x]]
risers (x : y : etc) = if x y then (x : s) : ss else [x] : (s : ss)
    where (s : ss) = risers (y : etc)

-- Desugared
let r1 = \a -> \b -> \c -> if b then (c : snd a) : (fst a) else (c : []) : (snd a : fst a)
 in let r2 = \d -> case d of (e:es) -> (es, e)
     in let rr = ( \u -> case u of { [] -> []; (v:vs) -> case vs of { [] -> (v : []) : []; (w:ws) -> r1 ((snd rr) w ws) (le v w) v } }
                 , \x -> \y -> r2 ((fst rr) (x : y))
                 )
         in fst rr
-}

exR0 = Let (name "r1") (Abs (name "a") (Abs (name "b") (Abs (name "c") (If "if" (Var $ name "b") (Cons (Cons (Var $ name "c") (Snd (Var $ name "a"))) (Fst (Var $ name "a"))) (Cons (Cons (Var $ name "c") (Nil)) (Cons (Snd (Var $ name "a")) (Fst (Var $ name "a"))))))))
       (Var $ name "r1")

exR0a = Let (name "r1") (Abs (name "a") (Abs (name "b") (Abs (name "c") (If "if" (Var $ name "b") (Cons (Cons (Var $ name "c") (Snd (Var $ name "a"))) (Fst (Var $ name "a"))) (Cons (Cons (Var $ name "c") (Nil)) (Cons (Snd (Var $ name "a")) (Fst (Var $ name "a"))))))))
       (App (App (App (Var $ name "r1") (Pair (Cons (Cons (Con $ Int 1) (Cons (Con $ Int 2) (Nil))) (Cons (Cons (Con $ Int 3) (Cons (Con $ Int 4) (Nil))) (Nil))) (Cons (Con $ Int 5) (Cons (Con $ Int 6) (Nil))))) (Con $ Bool True)) (Con $ Int 7))
       
exR0b = Let (name "r1") (Abs (name "a") (Abs (name "b") (Abs (name "c") (If "if" (Var $ name "b") (Cons (Cons (Var $ name "c") (Snd (Var $ name "a"))) (Fst (Var $ name "a"))) (Cons (Cons (Var $ name "c") (Nil)) (Cons (Snd (Var $ name "a")) (Fst (Var $ name "a"))))))))
       (App (App (App (Var $ name "r1") (Pair (Cons (Cons (Con $ Int 1) (Cons (Con $ Int 2) (Nil))) (Cons (Cons (Con $ Int 3) (Cons (Con $ Int 4) (Nil))) (Nil))) (Cons (Con $ Int 5) (Cons (Con $ Int 6) (Nil))))) (Con $ Bool False)) (Con $ Int 7))

exR1 = Let (name "r1") (Abs (name "a") (Abs (name "b") (Abs (name "c") (If "b" (Var $ name "b") (Cons (Cons (Var $ name "c") (Snd (Var $ name "a"))) (Fst (Var $ name "a"))) (Cons (Cons (Var $ name "c") (Nil)) (Cons (Snd (Var $ name "a")) (Fst (Var $ name "a"))))))))
       (Let (name "r2") (Abs (name "d") (Case "d" (Var $ name "d") (Nothing) (Just (name "e",name "es",Pair (Var $ name "es") (Var $ name "e")))))
       (Let (name "rl") (Fix (name "rf") (Pair (Abs (name "u") (Case "u" (Var $ name "u") (Just (Nil)) (Just (name "v",name "vs",Case "vs" (Var $ name "vs") (Just (Cons (Cons (Var $ name "v") (Nil)) (Nil))) (Just (name "w",name "ws",App (App (App (Var $ name "r1") (App (App (Snd (Var $ name "rf")) (Var $ name "w")) (Var $ name "ws"))) (Op LEQ (Var $ name "v") (Var $ name "w"))) (Var $ name "v"))))))) (Abs (name "x") (Abs (name "y") (App (Var $ name "r2") (App (Fst (Var $ name "rf")) (Cons (Var $ name "x") (Var $ name "y"))))))))
       (If "if" (Con $ Bool False)
        (App (Fst (Var $ name "rl")) Nil)
        (App (Fst (Var $ name "rl")) (Cons (Con $ Int 2) (Cons (Con $ Int 3) (Cons (Con $ Int 1) (Nil)))))
       )
    ))
    
exR1Nil = Let (name "r1") (Abs (name "a") (Abs (name "b") (Abs (name "c") (If "b" (Var $ name "b") (Cons (Cons (Var $ name "c") (Snd (Var $ name "a"))) (Fst (Var $ name "a"))) (Cons (Cons (Var $ name "c") (Nil)) (Cons (Snd (Var $ name "a")) (Fst (Var $ name "a"))))))))
       (Let (name "r2") (Abs (name "d") (Case "d" (Var $ name "d") (Nothing) (Just (name "e",name "es",Pair (Var $ name "es") (Var $ name "e")))))
       (Let (name "rl") (Fix (name "rf") (Pair (Abs (name "u") (Case "u" (Var $ name "u") (Just (Nil)) (Just (name "v",name "vs",Case "vs" (Var $ name "vs") (Just (Cons (Cons (Var $ name "v") (Nil)) (Nil))) (Just (name "w",name "ws",App (App (App (Var $ name "r1") (App (App (Snd (Var $ name "rf")) (Var $ name "w")) (Var $ name "ws"))) (Op LEQ (Var $ name "v") (Var $ name "w"))) (Var $ name "v"))))))) (Abs (name "x") (Abs (name "y") (App (Var $ name "r2") (App (Fst (Var $ name "rf")) (Cons (Var $ name "x") (Var $ name "y"))))))))
       (If "if" (Con $ Bool True)
        (App (Fst (Var $ name "rl")) Nil)
        (App (Fst (Var $ name "rl")) (Cons (Con $ Int 2) (Cons (Con $ Int 3) (Cons (Con $ Int 1) (Nil)))))
       )
    ))

{-
f x = case x of
        [] -> []
        (y:ys) -> case ys of
                    [] -> [y]
                    (z:zs) -> case f (z:zs) {- ys -} of
                                (a:as) -> (999:a:as)
-}

exRminimal = Fix _f (Abs _x (Case "case" (Var $ _x) (Just Nil) (Just (_y, _ys, Case "case" (Var $ _ys) (Just (Cons (Var $ _y) (Nil))) (Just (_z,_zs,Case "case" (App (Var $ _f) (Cons (Var $ _z) (Var $ _zs))) (Nothing) (Just (_a,_as,Cons (Con $ Int 999) (Cons (Var $ _a) (Var $ _as))))))))))
    
exRminimal0 = App exRminimal Nil
exRminimal1 = App exRminimal (Cons (Con $ Int 1) Nil)
exRminimal2 = App exRminimal (Cons (Con $ Int 1) (Cons (Con $ Int 2) (Cons (Con $ Int 3) (Nil))))

-- Length

testList :: Expr
testList = Cons (Con $ Int 1) (Cons (Con $ Int 2) (Cons (Con $ Int 3) (Nil)))

exLength, exLengthApp, exLengthBroken, exLengthBrokenApp :: Expr

exLength = Fix _f (Abs _xs (Case "case" (Var _xs) (Just (Con $ Int 0)) (Just (_a, _as, Op ADD (Con $ Int 1) (App (Var _f) (Var _as))))))

exLengthApp = Let (name "length") exLength (App (Var $ name "length") testList)

exLengthBroken = Fix _f (Abs _xs (Case "case" (Var _xs) (Nothing) (Just (_a, _as, Op ADD (Con $ Int 1) (App (Var _f) (Var _as))))))

exLengthBrokenApp = Let (name "lengthBroken") exLengthBroken (App (Var $ name "lengthBroken") testList)

{-
ex1 = Con (Bool True)
ex2 = Con (Int 42)
ex3 = Let x (Con (Int 42)) (Var x)
ex4 = Abs x (Con (Int 42))
ex5 = Abs x (Var x)
ex6 = App (Abs x (Con (Int 42))) (Con (Bool True))
ex7 = App (Abs x (Var x)) (Con (Bool True))
ex8 = Let const' (Abs k (Abs x (Var k))) (Var const')
ex9 = Let const' (Abs k (Abs x (Var k))) (App (Var const') (Con (Bool True)))
ex10 = Let const' (Abs k (Abs x (Var k))) (App (App (Var const') (Con (Bool True))) (Con (Int 42)))
ex11 = Let id' (Abs x (Var x)) (Var id')
ex12 = Let id' (Abs x (Var x)) (App (Var id') (Con (Bool False)))
ex13 = Abs "y" (Let const' (Abs k (Abs x (Var k))) (App (App (Var const') (Var "y")) (Con (Bool True))))
-}
