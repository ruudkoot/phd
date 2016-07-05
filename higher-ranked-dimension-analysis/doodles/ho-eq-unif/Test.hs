{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ViewPatterns           #-}

module Test where

import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Monad.Trans.List  (runListT)

import Data.Function
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Unif hiding (main, u0)

tests :: [(String, Bool)]
tests =
    [("for",                            test_for)
    ,("statefulForM (1)",               test_statefulForM_1)
    ,("statefulForM (2)",               test_statefulForM_2)
    ,("uncons (1)",                     test_uncons_1)
    ,("uncons (2)",                     test_uncons_2)
    ,("mapMaybeWithContext (1)",        test_mapMaybeWithContext_1)
    ,("(!!!)",                          test_III)
    ,("unionMap",                       test_unionMap)
    ,("unionMap'",                      test_unionMap')
    ,("base",                           test_base)
    ,("sig2ty",                         test_sig2ty)
    ,("sparsifySubst",                  test_sparsifySubst)
    ,("unFreeV",                        test_unFreeV)
    ,("isBound",                        test_isBound)
    ,("isFreeV",                        test_isFreeV)
    ,("isFreeC",                        test_isFreeC)
    ,("isConst",                        test_isConst)
    ,("hd",                             test_hd)
    ,("isRigid",                        test_isRigid)
    ,("bound",                          test_bound)
    ,("freeV (1)",                      test_freeV_1)
    ,("freeV (2)",                      test_freeV_2)
    ,("atom2term (Bound)",              test_atom2term_Bound)
    ,("atom2term (FreeV)",              test_atom2term_FreeV)
    ,("atom2term (FreeC)",              test_atom2term_FreeC)
    ,("atom2term (Const)",              test_atom2term_Const)
    ,("raise (1)",                      test_raise_1)
    ,("raise (2)",                      test_raise_2)
    ,("raise (3)",                      test_raise_3)
    ,("raise (4)",                      test_raise_4)
    ,("raise (5)",                      test_raise_5)
    ,("raise (6)",                      test_raise_6)
    ,("raise (7)",                      test_raise_7)
    ,("raise (8)",                      test_raise_8)
    ,("raise (9)",                      test_raise_9)
    ,("raise (10)",                     test_raise_10)
    ,("raise (11)",                     test_raise_11)
    ,("raise (12)",                     test_raise_12)
    ,("raise (13)",                     test_raise_13)
    ,("raise (14)",                     test_raise_14)
    ,("lower (1)",                      test_lower_1)
    ,("lower (2)",                      test_lower_2)
    --,("lower (3)",                    test_lower_3)     -- "raise: unexpected capture"
    --,("lower (4)",                    test_lower_4)     -- "raise: unexpected capture"
    ,("reduce (1)",                     test_reduce_1)
    ,("reduce (2)",                     test_reduce_2)
    ,("reduce (3)",                     test_reduce_3)
    ,("reduce (4)",                     test_reduce_4)
    ,("reduce (5)",                     test_reduce_5)
    -- FIXME: additional testcases for 'reduce' and 'bindAndReduce'
    ,("substFreeVAndReduce (1)",        test_substFreeVAndReduce_1)
    ,("typeOfAtom (Bound)",             test_typeOfAtom_Bound)
    ,("typeOfAtom (FreeV)",             test_typeOfAtom_FreeV)
    ,("typeOfAtom (FreeC)",             test_typeOfAtom_FreeC)
    ,("typeOfAtom (Const)",             test_typeOfAtom_Const)
    ,("typeOfFreeV (1)",                test_typeOfFreeV_1)
    ,("typeOfTerm (Bound)",             test_typeOfTerm_Bound)
    ,("typeOfTerm (FreeV)",             test_typeOfTerm_FreeV)
    ,("typeOfTerm (FreeC)",             test_typeOfTerm_FreeC)
    ,("typeOfTerm (Const)",             test_typeOfTerm_Const)
    ,("freshAtom (1)",                  test_freshAtom_1)
    ,("partialBinding (Bound,1)",       test_partialBinding_Bound_1)
    ,("partialBinding (Bound,2)",       test_partialBinding_Bound_2)
    ,("partialBinding (Bound,3)",       test_partialBinding_Bound_3)
    ,("partialBinding (FreeV,1)",       test_partialBinding_FreeV_1)
    ,("partialBinding (FreeV,2)",       test_partialBinding_FreeV_2)
    ,("partialBinding (FreeV,3)",       test_partialBinding_FreeV_3)
    ,("partialBinding (FreeV,4)",       test_partialBinding_FreeV_4)
    ,("partialBinding (FreeV,5)",       test_partialBinding_FreeV_5)
    ,("partialBinding (FreeV,6)",       test_partialBinding_FreeV_6)
    ,("partialBinding (FreeV,7)",       test_partialBinding_FreeV_7)
    ,("partialBinding (FreeC,1)",       test_partialBinding_FreeC_1)
    ,("partialBinding (FreeC,2)",       test_partialBinding_FreeC_2)
    ,("partialBinding (FreeC,3)",       test_partialBinding_FreeC_3)
    ,("partialBinding (FreeC,4)",       test_partialBinding_FreeC_4)
    ,("partialBinding (FreeC,5)",       test_partialBinding_FreeC_5)
    ,("partialBinding (FreeC,6)",       test_partialBinding_FreeC_6)
    ,("partialBinding (FreeC,7)",       test_partialBinding_FreeC_7)
    ,("partialBinding (Const,1)",       test_partialBinding_Const_1)
    ,("partialBinding (Const,2)",       test_partialBinding_Const_2)
    ,("partialBinding (Const,3)",       test_partialBinding_Const_3)
    ,("pmfs (1)",                       test_pmfs_1)
    ,("pmfs (2)",                       test_pmfs_2)
    ,("pmfs (3)",                       test_pmfs_3)
    ,("applyConditionalMapping (1)",    test_applyConditionalMapping_1)
    ,("applyConditionalMapping (2)",    test_applyConditionalMapping_2)
    ,("applyConditionalMapping (3)",    test_applyConditionalMapping_3)
    ,("applyOrderReduction (1)",        test_applyOrderReduction_1)
    ,("isTrivialFlexibleSubterm (1)",   test_isTrivialFlexibleSubterm_1)
    ,("isTrivialFlexibleSubterm (2)",   test_isTrivialFlexibleSubterm_2)
    ,("isTrivialFlexibleSubterm (3)",   test_isTrivialFlexibleSubterm_3)
    ,("isEAcceptable (1)",              test_isEAcceptable_1)
    ,("isEAcceptable (2)",              test_isEAcceptable_2)
    ,("isEAcceptable (3)",              test_isEAcceptable_3)
    ,("isEAcceptable (4)",              test_isEAcceptable_4)
    ,("transformAbs (1)",               test_transformAbs_1)
    ,("transformEUni (1)",              test_transformEUni_1)   -- FIXME: incomplete
    ,("transformBin (1)",               test_transformBin_1)    -- FIXME: incomplete
    ,("count (1)",                      test_count_1)
    ,("set (1)",                        test_set_1)
    ,("divides (1)",                    test_divides_1)
    ,("divides (2)",                    test_divides_2)
    ,("agIdSubst (1)",                  test_agIdSubst_1)
    ,("agApplySubst (1)",               test_agApplySubst_1)
    ,("agCompSubst (1)",                test_agCompSubst_1)
    ,("agUnif1 (1)",                    test_agUnif1_1)         -- FIXME: normal form
    ,("agUnif1 (1')",                   test_agUnif1_1')        -- FIXME: normal form
    ,("agUnif1 (2)",                    test_agUnif1_2)         -- FIXME: normal form
    ,("agUnif1' (1)",                   test_agUnif1'_1)
    ,("agUnif1' (1')",                  test_agUnif1'_1')
    ,("agConstMatch (1)",               test_agConstMatch_1)
    ,("agConstMatch (1')",              test_agConstMatch_1')
    ,("agConstMatch (2)",               test_agConstMatch_2)
    ,("agConstMatch (2')",              test_agConstMatch_2')
    ,("agConstMatch (3)",               test_agConstMatch_3)
    ,("newT (1)",                       test_newT_1)
    ,("newV (1)",                       test_newV_1)
    ,("isVar (1)",                      test_isVar_1)
    ,("vars (1)",                       test_vars_1)
    ,("vars' (1)",                      test_vars'_1)
    ,("allVars (1)",                    test_allVars_1)
    ,("homogeneous (1)",                test_homogeneous_1)
    ,("homogeneous' (1)",               test_homogeneous'_1)
    ,("homogeneous'' (1)",              test_homogeneous''_1)
    ,("homogeneous'' (2)",              test_homogeneous''_2)
    ,("homogeneous'' (3)",              test_homogeneous''_3)
    ,("isPureE",                        test_isPureE)
    ,("isPureE'",                       test_isPureE')
    ,("isHeterogeneous (1)",            test_isHeterogeneous_1)
    ,("isHeterogeneous (2)",            test_isHeterogeneous_2)
    ,("subst (1)",                      test_subst_1)
    ,("subst' (1)",                     test_subst'_1)
    ,("applySubst (1)",                 test_applySubst_1)
    ,("freeUnif (1)",                   test_freeUnif_1)    -- FIXME: test for each rule
    ,("freeUnif (2)",                   test_freeUnif_2)
    ,("classify (1)",                   test_classify_1)
    ,("classify (2)",                   test_classify_2)
    ,("inSolvedForm (1)",               test_inSolvedForm_1)
    ,("inSolvedForm (2)",               test_inSolvedForm_2)
    ,("inSolvedForm (3)",               test_inSolvedForm_3)
    ,("inSolvedForm (4)",               test_inSolvedForm_4)
    ,("numX",                           test_numX)
    ,("numX'",                          test_numX')
    ,("numC",                           test_numC)
    ,("toExp (1)",                      test_toExp_1)
    ,("toExp' (1)",                     test_toExp'_1)
    ,("fromExp (1)",                    test_fromExp_1)
    ,("dom (1)",                        test_dom_1)
    ,("domNotMappingToVar (1)",         test_domNotMappingToVar_1)
    ,("isShared (1)",                   test_isShared_1)
{-
    ,("agUnifN (VA, 1)",                test_agUnifN_VA_1)
    ,("agUnifN (E-Res, 1)",             test_agUnifN_ERes_1)
    ,("agUnifN (E-Res, 1')",            test_agUnifN_ERes_1')
    ,("agUnifN (E'-Res, 1)",            test_agUnifN_E'Res_1)
    ,("agUnifN (E-Match, 1)",           test_agUnifN_EMatch_1)
    ,("agUnifN (Merge-E-Match, 1)",     test_agUnifN_MergeEMatch_1)
    ,("agUnifN (Var-Rep, 1)",           test_agUnifN_VarRep_1)
    ,("agUnifN (Var-Rep, 1')",          test_agUnifN_VarRep_1')
    ,("agUnifN (Var-Rep, 1'')",         test_agUnifN_VarRep_1'')
    ,("agUnifN (Var-Rep, 1''')",        test_agUnifN_VarRep_1''')
    ,("agUnifN (Var-Rep, 2)",           test_agUnifN_VarRep_2)
    ,("agUnifN (Var-Rep, 2')",          test_agUnifN_VarRep_2')
    ,("agUnifN (Var-Rep, 2'')",         test_agUnifN_VarRep_2'')
    ,("agUnifN (Var-Rep, 2''')",        test_agUnifN_VarRep_2''')
    ,("agUnifN (Var-Rep, 3)",           test_agUnifN_VarRep_3)
    ,("agUnifN (Var-Rep, 3')",          test_agUnifN_VarRep_3')
    ,("agUnifN (Var-Rep, 3'')",         test_agUnifN_VarRep_3'')
    ,("agUnifN (Var-Rep, 3''')",        test_agUnifN_VarRep_3''')
    ,("agUnifN (Var-Rep, 4)",           test_agUnifN_VarRep_4)
    ,("agUnifN (Var-Rep, 4')",          test_agUnifN_VarRep_4')
    ,("agUnifN (Var-Rep, 4'')",         test_agUnifN_VarRep_4'')
    ,("agUnifN (Var-Rep, 4''')",        test_agUnifN_VarRep_4''')
    ,("agUnifN (Var-Rep, 5)",           test_agUnifN_VarRep_5)
-}
    ,("constantify (1)",                test_constantify_1)
    ,("deconstantify (1)",              test_deconstantify_1)
    ,("agUnif1TreatingAsConstant (1)",  test_agUnif1TreatingAsConstant_1)
    ,("agUnifN (1)",                    test_agUnifN_1)
    ,("agUnifN (2)",                    test_agUnifN_2)
    ,("agUnifN (3)",                    test_agUnifN_3)
    ]
    
len = maximum (map (length . fst) tests)
  
main = do
    putStrLn $ replicate 80 '='
    xs <- forM tests runTest
    putStrLn $ replicate 80 '='
    if and xs then
        putStrLn "All tests PASSED."
    else
        putStrLn "SOME TESTS FAILED!!!"
    
runTest (name, test) = do
    putStr   $ name ++ replicate (len - length name) ' ' ++ ": "
    putStrLn $ show test
    return test
    
(=?=) :: (Eq a, Show a) => a -> a -> Bool
x =?= y =
    if x == y then
        True
    else
        error $ "\n" ++ show x ++ "\n\n" ++ show y

-- | Utility | ------------------------------------------------------------[ ]--

test_for = for [0..9] (*2) == map (*2) [0..9]

test_statefulForM_1 = statefulForM (0::Int) [0..10] f =?= Just (11, [0,2..20])
    where f t x = return (t + 1, x + t)

test_statefulForM_2 = statefulForM (0::Int) [10,9..0] f =?= Nothing
    where f t x = if x - t > 0 then
                    return (t + 1, x - t)
                  else
                    fail "negative"
                    
test_uncons_1 = uncons ([]::[Int]) =?= Nothing

test_uncons_2 = uncons [1..9] =?= Just (1, [2..9])

test_mapMaybeWithContext_1 = mapMaybeWithContext f [1..9] =?= [43,41,39,37]
    where f x xs | even x    = Just (sum xs)
                 | otherwise = Nothing
                    
-- * Debugging * ----------------------------------------------------------[X]--

test_III = [0..10] !!! 10 =?= 10

-- * Sets * ---------------------------------------------------------------[X]--

test_unionMap = unionMap f (S.fromList [1,2,3]) =?= S.fromList [1,2,3,4,5]
    where f 1 = S.fromList [1,2,3]
          f 2 = S.fromList [2,3,4]
          f 3 = S.fromList [3,4,5]

test_unionMap' = unionMap' f [1,2,3] =?= S.fromList [1,2,3,4,5]
    where f 1 = S.fromList [1,2,3]
          f 2 = S.fromList [2,3,4]
          f 3 = S.fromList [3,4,5]

-- | General framework | --------------------------------------------------[ ]--

-- * Types * --------------------------------------------------------------[X]--

test_base = base Real =?= ([] :-> Real)

test_sig2ty = sig2ty ([Real,Real] :=> Real) =?= ([base Real, base Real] :-> Real)

test_sparsifySubst =
    let
        ty  n = replicate n (base Real) :-> Real
        arg n = A [] (Bound n) []
        tm  n = A (map ty [0..n-1]) (FreeV n) (map arg [0..n-1])
        fr  n = A (replicate n (base Real)) (FreeV n) (map (\x -> A [] (Bound x) []) [0..n-1])
        env n = map ty [0..n-1]
    in
        take 5 (sparsifySubst (env 5) ([(1,tm 1),(3, tm 3)] :: DenseSubst Sort Sig))
            =?= 
        [fr 0, tm 1, fr 2, tm 3, fr 4]

test_unFreeV = unFreeV (FreeV 9) =?= 9

test_isBound =
    map isBound [Bound undefined, FreeV undefined, FreeC undefined, Const Mul]
        =?=
    [True, False, False, False]
test_isFreeV = 
    map isFreeV [Bound undefined, FreeV undefined, FreeC undefined, Const Mul]
        =?=
    [False, True, False, False]
test_isFreeC = 
    map isFreeC [Bound undefined, FreeV undefined, FreeC undefined, Const Mul]
        =?=
    [False, False, True, False]
test_isConst = 
    map isConst [Bound undefined, FreeV undefined, FreeC undefined, Const Mul]
        =?=
    [False, False, False, True]

test_hd = hd (A undefined (Const Mul) undefined) =?= Const Mul

test_isRigid = 
    map isRigid [A undefined (Bound undefined) undefined
                ,A undefined (FreeV undefined) undefined
                ,A undefined (FreeC undefined) undefined
                ,A undefined (Const undefined) undefined]
        =?=
    [True, False, True, True]

test_bound =
    (bound [undefined,[base Real, base Real] :-> Real, undefined] 1 :: AlgebraicTerm Sort Sig)
        =?=
    A [base Real, base Real] (Bound 3) [A [] (Bound 0) [], A [] (Bound 1) []]

test_freeV_1 =
    (freeV [undefined,[base Real, base Real] :-> Real, undefined] 1 :: AlgebraicTerm Sort Sig)
        =?=
    A [base Real, base Real] (FreeV 1) [A [] (Bound 0) [], A [] (Bound 1) []]

test_freeV_2 =
    let
        ty  n = replicate n (base Real) :-> Real
        env   = map ty [0..]
    in
        (freeV env 2 :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real, base Real] (FreeV 2) [A [] (Bound 0) [], A [] (Bound 1) []]

test_atom2term_Bound =
    let envB = [undefined,[base Real, base Real] :-> Real,undefined]
        envV = undefined
        envC = undefined
     in (atom2term envB envV envC (Bound 1) :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real, base Real] (Bound 3) [A [] (Bound 0) [], A [] (Bound 1) []]

test_atom2term_FreeV =
    let envB = undefined
        envV = [undefined,[base Real, base Real] :-> Real,undefined]
        envC = undefined
     in (atom2term envB envV envC (FreeV 1) :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real, base Real] (FreeV 1) [A [] (Bound 0) [], A [] (Bound 1) []]

test_atom2term_FreeC =
    let envB = undefined
        envV = undefined
        envC = [undefined,[base Real, base Real] :-> Real,undefined]
     in (atom2term envB envV envC (FreeC 1) :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real, base Real] (FreeC 1) [A [] (Bound 0) [], A [] (Bound 1) []]

test_atom2term_Const =
    let envB = undefined
        envV = undefined
        envC = undefined
     in (atom2term envB envV envC (Const Mul) :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real, base Real] (Const Mul) [A [] (Bound 0) [], A [] (Bound 1) []]

-- * Substitution and reduction * -----------------------------------------[.]--

test_raise_1 =
    let tm = (A [] (FreeV 0) [A [] (FreeV 1) [], A [] (FreeV 2) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 tm
            =?=
        tm
        
test_raise_2 =
    let tm n = (A [] (FreeV 0) [A [] (FreeV 1) [], A [] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0)
            =?=
        (tm 10)
        
test_raise_3 =
    let tm n = (A [] (FreeV 0) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0)
            =?=
        (tm 0)

test_raise_4 =
    let tm n = (A [] (FreeV 0) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 1)
            =?=
        (tm 11)

test_raise_5 =
    let tm n = (A [base Real] (FreeV 0) [A [] (FreeV 1) [], A [] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0)
            =?=
        (tm 0)

test_raise_6 =
    let tm n = (A [base Real] (FreeV 0) [A [] (FreeV 1) [], A [] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 1)
            =?=
        (tm 11)

test_raise_7 =
    let tm n = (A [base Real] (FreeV 0) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0)
            =?=
        (tm 0)

test_raise_8 =
    let tm n = (A [base Real] (FreeV 0) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 1)
            =?=
        (tm 1)

test_raise_9 =
    let tm n = (A [base Real] (FreeV 0) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 2)
            =?=
        (tm 12)

test_raise_10 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0 0)
            =?=
        (tm 0 0)

test_raise_11 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 1 0)
            =?=
        (tm 11 0)

test_raise_12 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0 1)
            =?=
        (tm 0 1)

test_raise_13 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 0 2)
            =?=
        (tm 0 12)
        
test_raise_14 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in raise 10 (tm 1 2)
            =?=
        (tm 11 12)
        
test_lower_1 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in lower 10 (tm 0 1)
            =?=
        (tm 0 1)
        
test_lower_2 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in lower 1 (tm 2 3)
            =?=
        (tm 1 2)

test_lower_3 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in lower 2 (tm 2 4)
            =?=
        error "expected exception"

test_lower_4 =
    let tm m n = (A [base Real] (Bound m) [A [] (FreeV 1) [], A [base Real] (Bound n) []]
                    :: AlgebraicTerm Sort Sig)
     in lower 2 (tm 1 3)
            =?=
        error "expected exception"


-- (\x.x)(F1) --> F1
test_reduce_1 =
    let xs  = []
        xs' = [base Real]
        a   = Bound 0
        ys' = []
        ys  = [A [] (FreeV 0) []]
     in (reduce xs xs' a ys' ys :: AlgebraicTerm Sort Sig)
            =?=
        A [] (FreeV 0) []

-- (\xy.x(y))(\z.F1(z),F2) --> F1(F2)
test_reduce_2 =
    let xs  = []
        xs' = [[base Real] :-> Real, base Real]
        a   = Bound 0
        ys' = [A [] (Bound 1) []]
        ys  = [A [base Real] (FreeV 0) [A [] (Bound 0) []], A [] (FreeV 1) []]
     in (reduce xs xs' a ys' ys :: AlgebraicTerm Sort Sig)
            =?=
        A [] (FreeV 0) [A [] (FreeV 1) []]

-- \z.(\xy.x(y))(\u.F1(u),F2(z)) --> \z.F1(F2(z))
test_reduce_3 =
    let xs  = [base Real]
        xs' = [[base Real] :-> Real, base Real]
        a   = Bound 0
        ys' = [A [] (Bound 1) []]
        ys  = [A [base Real] (FreeV 0) [A [] (Bound 0) []], A [] (FreeV 1) [A [] (Bound 0) []]]
     in (reduce xs xs' a ys' ys :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real] (FreeV 0) [A [] (FreeV 1) [A [] (Bound 0) []]]

-- \z.(\xy.x(y))(\u.F1(u),F2(z)) --> \z.F1(F2(z))
test_reduce_4 =
    let xs  = [base Real]
        xs' = [[base Real] :-> Real, base Real]
        a   = Bound 0
        ys' = [A [] (Bound 1) []]
        ys  = [A [base Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []], A [] (FreeV 1) [A [] (Bound 0) []]]
     in (reduce xs xs' a ys' ys :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real] (FreeV 0) [A [] (FreeV 1) [A [] (Bound 0) []], A [] (Bound 0) []]

-- \uv.(\xy.y(\z.x(z)))(\p.v(p),\w.u(\q.w(q))) --> \uv.(u(\q.v(q)))
test_reduce_5 =
    let xs  = [[[base Real] :-> Real] :-> Real, [base Real] :-> Real]
        xs' = [[base Real] :-> Real, [[base Real] :-> Real] :-> Real]
        a   = Bound 1
        ys' = [A [base Real] (Bound 1) [A [] (Bound 0) []]]
        ys  = [A [base Real] (Bound 2) [A [] (Bound 0) []], A [[base Real] :-> Real] (Bound 1) [A [base Real] (Bound 1) [A [] (Bound 0) []]]]
    in (reduce xs xs' a ys' ys :: AlgebraicTerm Sort Sig)
            =?=
       A [[[base Real] :-> Real] :-> Real, [base Real] :-> Real] (Bound 0) [A [base Real] (Bound 2) [A [] (Bound 0) []]]

-- F1(F2,F0)[apply/F1;id/F2] --> F0
test_substFreeVAndReduce_1 =
    let tm      = A [base Real]
                    (FreeV 1)
                    [ A [ [base Real] :-> Real
                        , base Real]
                        (FreeV 2)
                        [ A [base Real] (Bound 1) [A [] (Bound 0) []]
                        , A [] (Bound 1) [] ]
                    , A [base Real] (FreeV 0) [A [] (Bound 0) []]
                    , A [] (Bound 0) [] ]
        tmApply = A [ [[[base Real] :-> Real] :-> Real] :-> Real
                    , [base Real] :-> Real
                    , base Real]
                    (Bound 0)
                    [ A [base Real] (Bound 2) [A [] (Bound 0) []]
                    , A [] (Bound 2) []]
        tmId    = A [ [base Real] :-> Real, base Real]
                    ( Bound 0 )
                    [ A [] (Bound 1) [] ]
        tmF0    = A [ base Real ]
                    ( FreeV 0 )
                    [ A [] (Bound 0) [] ]
    in substFreeVAndReduce [tmF0, tmApply, tmId] tm
            =?=
       (tmF0 :: AlgebraicTerm Sort Sig)
        
-- * Partial bindings * ---------------------------------------------------[X]--

test_typeOfAtom_Bound =
    let envB = [[base Real] :-> Real] :: Env Sort
        envV = []
        envC = []
        atom = Bound 0 :: Atom Sig
     in runState (typeOfAtom envB atom) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))
        
test_typeOfAtom_FreeV =
    let envB = []
        envV = [[base Real] :-> Real] :: Env Sort
        envC = []
        atom = FreeV 0 :: Atom Sig
     in runState (typeOfAtom envB atom) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))
        
test_typeOfAtom_FreeC =
    let envB = []
        envV = []
        envC = [[base Real] :-> Real] :: Env Sort
        atom = FreeC 0 :: Atom Sig
     in runState (typeOfAtom envB atom) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))
        
test_typeOfAtom_Const =
    let envB = [] :: Env Sort
        envV = []
        envC = []
        atom = Const Mul
     in runState (typeOfAtom envB atom) (envV, envC)
            =?=
        ([base Real, base Real] :-> Real,(envV,envC))

test_typeOfFreeV_1 =
    let envV = [[base Real] :-> Real] :: Env Sort
        envC = []
     in runState (typeOfFreeV 0) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))

test_typeOfTerm_Bound =
    let envB = [[base Real] :-> Real] :: Env Sort
        envV = []
        envC = []
        tm   = A [base Real] (Bound 1) [A [] (Bound 0) []] :: AlgebraicTerm Sort Sig
     in runState (typeOfTerm envB tm) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))
        
test_typeOfTerm_FreeV =
    let envB = []
        envV = [[base Real] :-> Real] :: Env Sort
        envC = []
        tm   = A [base Real] (FreeV 0) [A [] (Bound 0) []] :: AlgebraicTerm Sort Sig
     in runState (typeOfTerm envB tm) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))
        
test_typeOfTerm_FreeC =
    let envB = []
        envV = []
        envC = [[base Real] :-> Real] :: Env Sort
        tm   = A [base Real] (FreeC 0) [A [] (Bound 0) []] :: AlgebraicTerm Sort Sig
     in runState (typeOfTerm envB tm) (envV, envC)
            =?=
        ([base Real] :-> Real,(envV,envC))
        
test_typeOfTerm_Const =
    let envB = [[base Real] :-> Real] :: Env Sort
        envV = []
        envC = []
        tm   = A [base Real,base Real] (Const Mul) [A [] (Bound 0) [],A [] (Bound 1) []] :: AlgebraicTerm Sort Sig
     in runState (typeOfTerm envB tm) (envV, envC)
            =?=
        ([base Real, base Real] :-> Real,(envV,envC))
        
test_freshAtom_1 =
    let envV = [[base Real]                       :-> Real] :: Env Sort
        envC = [[base Real, base Real]            :-> Real]
        ty   = [base Real, base Real, base Real] :-> Real
     in runState (freshAtom ty) (envV, envC)
            =?=
        (FreeV 1 :: Atom Sig,(envV ++ [ty],envC))

test_partialBinding_Bound_1 =
    let ty   = [base Real,[base Real,base Real]:->Real,[[base Real]:->Real]:->Real] :-> Real
        atom = Bound 0 :: Atom Sig
        envV = []
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real,[[] :-> Real,[] :-> Real] :-> Real,[[[] :-> Real] :-> Real] :-> Real] (Bound 0) []
        ,(envV,envC))

test_partialBinding_Bound_2 =
    let ty   = [base Real,[base Real,base Real]:->Real,[[base Real]:->Real]:->Real] :-> Real
        atom = Bound 1 :: Atom Sig
        envV = []
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real,[[] :-> Real,[] :-> Real] :-> Real,[[[] :-> Real] :-> Real] :-> Real] (Bound 1) [A [] (FreeV 0) [A [] (Bound 0) [],A [[] :-> Real,[] :-> Real] (Bound 3) [A [] (Bound 0) [],A [] (Bound 1) []],A [[[] :-> Real] :-> Real] (Bound 3) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]]],A [] (FreeV 1) [A [] (Bound 0) [],A [[] :-> Real,[] :-> Real] (Bound 3) [A [] (Bound 0) [],A [] (Bound 1) []],A [[[] :-> Real] :-> Real] (Bound 3) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]]]]
        ,(envV ++ [[[] :-> Real,[[] :-> Real,[] :-> Real] :-> Real,[[[] :-> Real] :-> Real] :-> Real] :-> Real,[[] :-> Real,[[] :-> Real,[] :-> Real] :-> Real,[[[] :-> Real] :-> Real] :-> Real] :-> Real],envC))

test_partialBinding_Bound_3 =
    let ty   = [base Real,[base Real,base Real]:->Real,[[base Real]:->Real]:->Real] :-> Real
        atom = Bound 2 :: Atom Sig
        envV = []
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real,[[] :-> Real,[] :-> Real] :-> Real,[[[] :-> Real] :-> Real] :-> Real] (Bound 2) [A [[] :-> Real] (FreeV 0) [A [] (Bound 1) [],A [[] :-> Real,[] :-> Real] (Bound 4) [A [] (Bound 0) [],A [] (Bound 1) []],A [[[] :-> Real] :-> Real] (Bound 4) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]],A [] (Bound 0) []]]
        ,(envV ++ [[[] :-> Real,[[] :-> Real,[] :-> Real] :-> Real,[[[] :-> Real] :-> Real] :-> Real,[] :-> Real] :-> Real],envC))

test_partialBinding_FreeV_1 =
    let ty   = base Real
        atom = FreeV 0 :: Atom Sig
        envV = [base Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (FreeV 0) [],(envV,envC))

test_partialBinding_FreeV_2 =
    let ty   = [base Real] :-> Real
        atom = FreeV 0 :: Atom Sig
        envV = [base Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (FreeV 0) [],(envV,envC))

test_partialBinding_FreeV_3 =
    let ty   = base Real
        atom = FreeV 0 :: Atom Sig
        envV = [[base Real] :-> Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (FreeV 0) [A [] (FreeV 1) []]
        ,(envV ++ [[] :-> Real],envC))
        
test_partialBinding_FreeV_4 =
    let ty   = [base Real] :-> Real
        atom = FreeV 0 :: Atom Sig
        envV = [[base Real] :-> Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (FreeV 0) [A [] (FreeV 1) [A [] (Bound 0) []]]
        ,(envV ++ [[[] :-> Real] :-> Real],envC))
        
test_partialBinding_FreeV_5 =
    let ty   = base Real
        atom = FreeV 0 :: Atom Sig
        envV = [[[base Real]:->Real,base Real] :-> Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (FreeV 0) [A [[] :-> Real] (FreeV 1) [A [] (Bound 0) []],A [] (FreeV 2) []]
        ,(envV ++ [[[] :-> Real] :-> Real,[] :-> Real],envC))

test_partialBinding_FreeV_6 =
    let ty   = [base Real] :-> Real
        atom = FreeV 0 :: Atom Sig
        envV = [[[base Real]:->Real,base Real] :-> Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (FreeV 0) [A [[] :-> Real] (FreeV 1) [A [] (Bound 1) [],A [] (Bound 0) []],A [] (FreeV 2) [A [] (Bound 0) []]]
        ,(envV ++ [[[] :-> Real,[] :-> Real] :-> Real,[[] :-> Real] :-> Real],envC))

test_partialBinding_FreeV_7 =
    let ty   = [base Real,[base Real]:->Real] :-> Real
        atom = FreeV 0 :: Atom Sig
        envV = [[[base Real]:->Real,base Real] :-> Real]
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real,[[] :-> Real] :-> Real] (FreeV 0) [A [[] :-> Real] (FreeV 1) [A [] (Bound 1) [],A [[] :-> Real] (Bound 3) [A [] (Bound 0) []],A [] (Bound 0) []],A [] (FreeV 2) [A [] (Bound 0) [],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]]]
        ,(envV ++ [[[] :-> Real,[[] :-> Real] :-> Real,[] :-> Real] :-> Real,[[] :-> Real,[[] :-> Real] :-> Real] :-> Real],envC))

test_partialBinding_FreeC_1 =
    let ty   = base Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [base Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (FreeC 0) [],(envV,envC))

test_partialBinding_FreeC_2 =
    let ty   = [base Real] :-> Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [base Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (FreeC 0) [],(envV,envC))

test_partialBinding_FreeC_3 =
    let ty   = base Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [[base Real] :-> Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (FreeC 0) [A [] (FreeV 0) []]
        ,(envV ++ [[] :-> Real],envC))
        
test_partialBinding_FreeC_4 =
    let ty   = [base Real] :-> Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [[base Real] :-> Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (FreeC 0) [A [] (FreeV 0) [A [] (Bound 0) []]]
        ,(envV ++ [[[] :-> Real] :-> Real],envC))
        
test_partialBinding_FreeC_5 =
    let ty   = base Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [[[base Real]:->Real,base Real] :-> Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (FreeC 0) [A [[] :-> Real] (FreeV 0) [A [] (Bound 0) []],A [] (FreeV 1) []]
        ,(envV ++ [[[] :-> Real] :-> Real,[] :-> Real],envC))

test_partialBinding_FreeC_6 =
    let ty   = [base Real] :-> Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [[[base Real]:->Real,base Real] :-> Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (FreeC 0) [A [[] :-> Real] (FreeV 0) [A [] (Bound 1) [],A [] (Bound 0) []],A [] (FreeV 1) [A [] (Bound 0) []]]
        ,(envV ++ [[[] :-> Real,[] :-> Real] :-> Real,[[] :-> Real] :-> Real],envC))

test_partialBinding_FreeC_7 =
    let ty   = [base Real,[base Real]:->Real] :-> Real
        atom = FreeC 0 :: Atom Sig
        envV = []
        envC = [[[base Real]:->Real,base Real] :-> Real]
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real,[[] :-> Real] :-> Real] (FreeC 0) [A [[] :-> Real] (FreeV 0) [A [] (Bound 1) [],A [[] :-> Real] (Bound 3) [A [] (Bound 0) []],A [] (Bound 0) []],A [] (FreeV 1) [A [] (Bound 0) [],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]]]
        ,(envV ++ [[[] :-> Real,[[] :-> Real] :-> Real,[] :-> Real] :-> Real,[[] :-> Real,[[] :-> Real] :-> Real] :-> Real],envC))

test_partialBinding_Const_1 =
    let ty   = base Real
        atom = Const Mul :: Atom Sig
        envV = []
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [] (Const Mul) [A [] (FreeV 0) [],A [] (FreeV 1) []]
        ,(envV ++ [base Real, base Real],envC))

test_partialBinding_Const_2 =
    let ty   = [base Real] :-> Real
        atom = Const Mul :: Atom Sig
        envV = []
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real] (Const Mul) [A [] (FreeV 0) [A [] (Bound 0) []],A [] (FreeV 1) [A [] (Bound 0) []]]
        ,(envV ++ [[base Real] :-> Real, [base Real] :-> Real],envC))

test_partialBinding_Const_3 =
    let ty   = [base Real,[base Real]:->Real] :-> Real
        atom = Const Mul :: Atom Sig
        envV = []
        envC = []
     in runState (partialBinding ty atom) (envV,envC)
            =?=
        (A [[] :-> Real,[[] :-> Real] :-> Real] (Const Mul) [A [] (FreeV 0) [A [] (Bound 0) [],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]],A [] (FreeV 1) [A [] (Bound 0) [],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]]]
        ,(envV ++ [[base Real,[base Real]:->Real]:->Real, [base Real,[base Real]:->Real]:->Real],envC))

-- * Maximal flexible subterms (Qian & Wang) * ----------------------------[X]--

-- Qian & Wang (p. 407)

t1, u0, u1 :: AlgebraicTerm Sort Sig

-- \x.F(x)*G(x)*x === \x.*(F(x),*(G(x),x))
t1 = A  [base Real]
        (Const Mul)
        [A  [] (FreeV 0) [A [] (Bound 0) []]
        ,A  []
            (Const Mul)
            [A [] (FreeV 1) [A [] (Bound 0) []]
            ,A [] (Bound 0) []
            ]
        ]

u0 = A [base Real, base Real]
       (FreeC 0)
       [ A [] (FreeV 0) [A [] (Bound 0) []]
       , A [base Real] (FreeV 0) [A [] (Bound 1) []]
       , A [] (FreeV 1) [A [] (FreeV 0) [A [] (Bound 0) []]]]

-- \x:R->R\y:R->R.C(F(\p:R.x(p)),\z:R->R.F(\q:R.x(q)),\r:R->R.G(F(\s:R.x(s)),\t:R.r(t)))
u1 = A [[base Real] :-> Real, [base Real] :-> Real]
       (FreeC 0)
       [ A [] (FreeV 0) [A [base Real] (Bound 1) [A [] (Bound 0) []]]
       , A [[base Real] :-> Real] (FreeV 0) [A [base Real] (Bound 2) [A [] (Bound 0) []]]
       , A [[base Real] :-> Real]
           (FreeV 1)
           [A [] (FreeV 0) [A [base Real] (Bound 2) [A [] (Bound 0) []]]
           ,A [base Real] (Bound 1) [A [] (Bound 0) []]]
       ]

test_pmfs_1 =
    let tm = t1
     in S.toList (pmfs tm)
            =?=
        [([[] :-> Real],A [] (FreeV 0) [A [] (Bound 0) []])
        ,([[] :-> Real],A [] (FreeV 1) [A [] (Bound 0) []])]

test_pmfs_2 =
    let tm = u0
     in S.toList (pmfs tm)
            =?=
        [([[] :-> Real,[] :-> Real],
            A [] (FreeV 0) [A [] (Bound 0) []])
        ,([[] :-> Real,[] :-> Real],
            A [] (FreeV 1) [A [] (FreeV 0) [A [] (Bound 0) []]])
        ,([[] :-> Real,[] :-> Real,[] :-> Real],
            A [] (FreeV 0) [A [] (Bound 1) []])
        ]

test_pmfs_3 =
    let tm = u1
     in S.toList (pmfs tm)
            =?=
        [([[[] :-> Real] :-> Real,[[] :-> Real] :-> Real]
          ,A [] (FreeV 0) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]])
        ,([[[] :-> Real] :-> Real,[[] :-> Real] :-> Real,[[] :-> Real] :-> Real]
          ,A [] (FreeV 0) [A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]])
        ,([[[] :-> Real] :-> Real,[[] :-> Real] :-> Real,[[] :-> Real] :-> Real]
          ,A [] (FreeV 1)
            [A [] (FreeV 0) [A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]]
            ,A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]])]

test_applyConditionalMapping_1 =
    let tm      = t1
        condMap = M.fromList $ [(([[] :-> Real],A [] (FreeV 0) [A [] (Bound 0) []])
                                    ,FreeV 2)
                               ,(([[] :-> Real],A [] (FreeV 1) [A [] (Bound 0) []])
                                    ,FreeV 3)]
     in applyConditionalMapping condMap tm
            =?=
        -- \x.*(F2(x),*(F3(x),x))
        A   [[] :-> Real]
            (Const Mul)
            [A  [] 
                (FreeV 2)
                [A [] (Bound 0) []]
                ,A [] (Const Mul) [A [] (FreeV 3) [A [] (Bound 0) []]
                                  ,A [] (Bound 0) []]]

test_applyConditionalMapping_2 =
    let tm      = u0
        condMap = M.fromList $ [(([base Real,base Real]
                                 ,A [] (FreeV 0) [A [] (Bound 0) []])
                                ,FreeV 2)
                               ,(([base Real,base Real,base Real]
                                 ,A [] (FreeV 0) [A [] (Bound 1) []])
                                ,FreeV 3)
                               ,(([base Real,base Real]
                                 ,A [] (FreeV 1) [A [] (FreeV 0) [A [] (Bound 0) []]])
                                ,FreeV 4)]
     in applyConditionalMapping condMap tm
            =?=
        A   [[] :-> Real,[] :-> Real]
            (FreeC 0)
            [A [] (FreeV 2) [A [] (Bound 0) [],A [] (Bound 1) []]
            ,A [[] :-> Real] (FreeV 3) [A [] (Bound 0) [],A [] (Bound 1) [],A [] (Bound 2) []]
            ,A [] (FreeV 4) [A [] (Bound 0) [],A [] (Bound 1) []]]

test_applyConditionalMapping_3 =
    let tm      = u1
        condMap = M.fromList $
            [(([[base Real]:->Real,[base Real]:->Real]
              ,A [] (FreeV 0) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]])
             ,FreeV 2)
            ,(([[base Real]:->Real,[base Real]:->Real,[base Real]:->Real]
              ,A [] (FreeV 0) [A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]])
             ,FreeV 3)
            ,(([[base Real] :-> Real,[base Real]:->Real,[base Real]:->Real]
              ,A [] (FreeV 1)
                [A [] (FreeV 0) [A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]]
                ,A [[] :-> Real] (Bound 1) [A [] (Bound 0) []]])
             ,FreeV 4)]
     in applyConditionalMapping condMap tm
            =?=
        A [[[] :-> Real] :-> Real,[[] :-> Real] :-> Real] (FreeC 0) [A [] (FreeV 2) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []]],A [[[] :-> Real] :-> Real] (FreeV 3) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []],A [[] :-> Real] (Bound 3) [A [] (Bound 0) []]],A [[[] :-> Real] :-> Real] (FreeV 4) [A [[] :-> Real] (Bound 1) [A [] (Bound 0) []],A [[] :-> Real] (Bound 2) [A [] (Bound 0) []],A [[] :-> Real] (Bound 3) [A [] (Bound 0) []]]]

test_applyOrderReduction_1 =
    let tm          = t1
        ordRedMap   = M.fromList [(A [] (FreeV 0) [A [] (Bound 0) []],FreeV 2)
                                 ,(A [] (FreeV 1) [A [] (Bound 0) []],FreeV 3)]
     in applyOrderReduction ordRedMap tm
            =?=
        -- \x.*(F2,*(F3,x))
        A   [[] :-> Real]
            (Const Mul)
            [A [] (FreeV 2) []
            ,A [] (Const Mul) [A [] (FreeV 3) [],A [] (Bound 0) []]]
            
test_isTrivialFlexibleSubterm_1 =
    let env = [base Real, base Real]
        tm  = A []
                (FreeV 1)
                [A [] (Bound 0) [], A [] (Bound 1) []]
     in isTrivialFlexibleSubterm env (tm :: AlgebraicTerm Sort Sig)
            =?=
        True
        
test_isTrivialFlexibleSubterm_2 =
    let env = [[base Real] :-> Real]
        tm  = A []
                (FreeV 0)
                [A [base Real] (Bound 1) [A [] (Bound 0) []]]
     in isTrivialFlexibleSubterm env (tm :: AlgebraicTerm Sort Sig)
            =?=
        True
        
test_isTrivialFlexibleSubterm_3 =
    let env = [base Real]
        tm  = A []
                (FreeV 0)
                [A [] (FreeV 1) []]
     in isTrivialFlexibleSubterm env (tm :: AlgebraicTerm Sort Sig)
            =?=
        False           
        
-- \x.f(\y.(F(y,x))) =?= \x.G(x)      [note that the aruments of F are permuted]
test_isEAcceptable_1 =
    let termSystem = [(A [base Real]
                         (FreeC 0)
                         [A [base Real] (FreeV 0) [A [] (Bound 0) []
                                                  ,A [] (Bound 1) []]]
                      ,A [base Real]
                         (FreeC 1)
                         [A [] (Bound 0) []]
                      )]
     in isEAcceptable (termSystem :: TermSystem Sort Sig)
            =?=
        True

test_isEAcceptable_2 =
    let termSystem = [(A [] (FreeV 0) [A [] (FreeC 0) []],A [] (FreeC 0) [])]
     in isEAcceptable (termSystem :: TermSystem Sort Sig)
            =?=
        False
        
test_isEAcceptable_3 =
    let termSystem = [(A [] (FreeC 0) [A [] (FreeV 0) []
                                      ,A [base Real] (FreeV 0) []]
                      ,A [] (FreeC 1) [])]
     in isEAcceptable (termSystem :: TermSystem Sort Sig)
            =?=
        False
        
test_isEAcceptable_4 =
    let termSystem = [(A [base Real] (FreeV 0) [A [] (Bound 0) []]
                      ,A [base Real] (Const Mul)
                         [A [] (FreeV 0) [A [] (Bound 0) []]
                         ,A [] (Const Mul)
                             [A [] (FreeV 1) [A [] (Bound 0) []]
                             ,A [] (Bound 0) []]
                         ]
                      )]
     in isEAcceptable (termSystem :: TermSystem Sort Sig)
            =?=
        True

-- * Transformation rules (Qian & Wang) * ---------------------------------[ ]--

-- FIXME: this example is "meh", as it is already E-acceptable and the
--        application of theta' is an identity.
-- \x.F(x) =?= \x.F(x)*G(x)*x
--         === \x.*(F(x),*(G(x),x))
test_transformAbs_1 =
    let subst      = [A [base Real] (FreeV 0) [A [] (Bound 0) []]
                      ,A [base Real] (FreeV 1) [A [] (Bound 0) []]]
        termPair   = (A [base Real] (FreeV 0) [A [] (Bound 0) []]
                      ,A [base Real] (Const Mul)
                         [A [] (FreeV 0) [A [] (Bound 0) []]
                         ,A [] (Const Mul)
                             [A [] (FreeV 1) [A [] (Bound 0) []]
                             ,A [] (Bound 0) []]
                         ]
                      )
        termSystem = []
        envV       = [[base Real] :-> Real, [base Real] :-> Real]
        envC       = []
     in runState (transformAbs (subst,termPair,termSystem)) (envV,envC)
          =?=
        (Just ( -- substitution
                subst ++
                [A [[] :-> Real] (FreeV 0) [A [] (Bound 0) []]
                ,A [[] :-> Real] (FreeV 1) [A [] (Bound 0) []]]
              , -- term system
                [(A [[] :-> Real]
                    (FreeV 2)
                    [A [] (Bound 0) []]
                 ,A [[] :-> Real] 
                    (Const Mul)
                    [A [] (FreeV 2) [A [] (Bound 0) []]
                    ,A [] (Const Mul) [A [] (FreeV 3) [A [] (Bound 0) []]
                                      ,A [] (Bound 0) []]])


                ,(A [[] :-> Real]
                    (FreeV 2) 
                    [A [] (Bound 0) []]
                 ,A [[] :-> Real]
                    (FreeV 0)
                    [A [] (Bound 0) []])


                ,(A [[] :-> Real]
                    (FreeV 3)
                    [A [] (Bound 0) []]
                 ,A [[] :-> Real] 
                    (FreeV 1)
                    [A [] (Bound 0) []])]
              )
         , -- environment
           ( envV ++ [[base Real] :-> Real, [base Real] :-> Real]
           , envC )
         )

-- \x.F(x) =?= \x.F(x)*G(x)*x
--         === \x.*(F(x),*(G(x),x))
test_transformEUni_1 =
    let subst       = [A [base Real] (FreeV 0) [A [] (Bound 0) []]
                      ,A [base Real] (FreeV 1) [A [] (Bound 0) []]]
        termSystem' = [(A [base Real] (FreeV 0) [A [] (Bound 0) []]
                       ,A [base Real] (Const Mul)
                          [A [] (FreeV 0) [A [] (Bound 0) []]
                          ,A [] (Const Mul)
                              [A [] (FreeV 1) [A [] (Bound 0) []]
                              ,A [] (Bound 0) []]
                          ]
                      )]
        termSystem  = []
        envV        = [[base Real] :-> Real, [base Real] :-> Real]
        envC        = []

        (Just (theta',ss),(envV',envC'))
            = runState (transformEUni (subst,termSystem',termSystem)) (envV,envC)
            
     in ss =?= 
            [(A [[] :-> Real] (FreeV 0) [A [] (Bound 0) []]
             ,A [[] :-> Real] (Const Mul) [A [] (FreeV 6) [A [] (Bound 0) []]
                                          ,A [] (Const Mul) [A [] (Bound 0) []
                                                            ,A [] (FreeV 7) [A [] (Bound 0) []]]])
            ,(A [[] :-> Real] (FreeV 1) [A [] (Bound 0) []]
             ,A [[] :-> Real] (FreeV 6) [A [] (Bound 0) []])]
        &&
            envV'
                =?=
            [[[] :-> Real] :-> Real     -- F0 / F
            ,[[] :-> Real] :-> Real     -- F1 / G
            ,[] :-> Real                -- F2 / Y1  (temp)
            ,[] :-> Real                -- F3 / Y2  (temp)
            ,[] :-> Real                -- F4 / Z1  (temp)
            ,[] :-> Real                -- F5 / Z2  (temp)
            ,[[] :-> Real] :-> Real     -- F6 / Z1'
            ,[[] :-> Real] :-> Real]    -- F7 / Z2'
        &&
            envC' =?= []

-- FIXME: test if substitutions are applied correctly to S
-- FIXME: test if theta' is updated correctly
-- FIXME: test_transformBin_2: more interesting types and terms
test_transformBin_1 =
    let subst       = error "subst"
        termPair    = (A [] (FreeV 0)   [A [] (FreeC 0) [], A [] (FreeC 1) []]
                      ,A [] (Const Mul) [A [] (FreeC 1) [], A [] (FreeC 0) []])
                            :: TermPair Sort Sig
        termSystem  = []
        envV        = [[base Real, base Real] :-> Real]
        envC        = [base Real, base Real]

        (xs,(envV',envC'))
            = runState (transformBin (subst,termPair,termSystem)) (envV, envC)
            
     in map snd xs
            =?=
        -- projection (Bound)
        [[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (Bound 0) [])]

        ,[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (Bound 1) [])]

        -- imitation (Const)
        ,[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (Const Mul)
                [A [] (FreeV 1) [A [] (Bound 0) [],A [] (Bound 1) []]
                ,A [] (FreeV 2) [A [] (Bound 0) [],A [] (Bound 1) []]])]

        ,[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (Const Inv)
                [A [] (FreeV 3) [A [] (Bound 0) [],A [] (Bound 1) []]])]

        ,[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (Const Unit) [])]

        -- imitation (FreeC)
        ,[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (FreeC 0) [])]

        ,[(A [[] :-> Real,[] :-> Real] (FreeV 0) [A [] (Bound 0) [],A [] (Bound 1) []]
          ,A [[] :-> Real,[] :-> Real] (FreeC 1) [])]]

        && envV' =?= (envV ++ envV ++ envV ++ envV)
        
        && envC' =?= envC
            
-- * Control strategy (Qian & Wang) * -------------------------------------[ ]--


-- | Higher-order dimension types | ---------------------------------------[ ]--


-- | Unification modulo Abelian groups | ----------------------------------[ ]--

-- * AG-unification with free nullary constants * -------------------------[X]--

test_count_1 = count odd [1..9] =?= 5

test_set_1 = set "abcdefghij" 4 'E' =?= "abcdEfghij"

test_divides_1 = 5 `divides` 10 =?= True
test_divides_2 = 5 `divides` 11 =?= False

test_agIdSubst_1 =
    agIdSubst 3 2
        =?=
    [([1,0,0],[0,0])
    ,([0,1,0],[0,0])
    ,([0,0,1],[0,0])]

test_agApplySubst_1 =
    let ss  = [([0,1,2],[3,4])
              ,([5,6,7],[8,9])
              ,([0,2,4],[6,8])]
        exp = ([1,2,3],[4,5])
     in agApplySubst ss exp
            =?=
        ([10,19,28],[41,51])

test_agCompSubst_1 =
    let ss = [([0,1],[2])
             ,([3,4],[5])]
        us = [([1,3],[5])
             ,([2,4],[6])]
     in agCompSubst ss us
            =?=
        [([ 9,13],[22])
        ,([12,18],[30])]

-- Lankford, Butler & Brady (EXAMPLE 1)
-- FIXME: not in (Hermite?) normal form...
test_agUnif1_1 =
    let exp = ([2,3,-1,-4],[-5])
     in agUnif1 exp
            =?=
        Just [([ 1, 0, 0, 0],[ 0])
             ,([ 0, 1, 0, 0],[ 0])
             ,([ 2, 3, 0,-4],[-5])
             ,([ 0, 0, 0, 1],[ 0])]
             
test_agUnif1_1' =
    let exp = ([2,3,-1,-4],[-5])
     in agApplySubst (fromJust $ agUnif1 exp) exp
            =?=
        ([0,0,0,0],[0])

-- Lankford, Butler & Brady (EXAMPLE 2)
-- FIXME: not in (Hermite?) normal form...
test_agUnif1_2 =
    let exp = ([3827,-2223,1934,-3400,8418,-6646,7833,-9433,4584,-4462],[])
     in agApplySubst (fromJust $ agUnif1 exp) exp
            =?=
        (replicate 10 0, [])

{-
        Just [([   1,    0, 0,    0,    0,    0,    0,   0,    0,   0],[])
             ,([   0,    1, 0,    0,    0,    0,    0,   0,    0,   0],[])
             ,([ 977, -678, 0,  680, 1953, 1166, -129, 320,  381,  74],[])
             ,([   0,    0, 0,    1,    0,    0,    0,   0,    0,   0],[])
             ,([  44,  -31, 0,   34,   91,   53,   -2,  16,   18,   4],[])
             ,([   0,    0, 0,    0,    0,    1,    0,   0,    0,   0],[])
             ,([-289,  201, 0, -204, -580, -344,   34, -95, -114, -22],[])
             ,([   0,    0, 0,    0,    0,    0,    0,   1,    0,   0],[])
             ,([   0,    0, 0,    0,    0,    0,    0,   0,    1,   0],[])
             ,([   0,    0, 0,    0,    0,    0,    0,   0,    0,   1],[])]
-}

test_agUnif1'_1 =
    let exps = [([3,-4,0],[])
               ,([0,2,-3],[])]
     in agUnif1' exps
            =?=
        Just [([0,4,0],[])
             ,([0,3,0],[])
             ,([0,2,0],[])]

test_agUnif1'_1' =
    let exps = [([3,-4,0],[])
               ,([0,2,-3],[])]
     in map (agApplySubst (fromJust $ agUnif1' exps)) exps
            =?=
        [([0,0,0],[]),([0,0,0],[])]
        
-- FIXME: add Example 1 (p. 452)

test_agConstMatch_1 =
    let exp1 = ([1,1,0],[1,1])
        exp2 = ([0,0,0],[1,0])
     in agConstMatch exp1 exp2
            =?=
        Just [([0,-1,0],[0,-1])
             ,([0, 1,0],[0, 0])
             ,([0, 0,1],[0, 0])
             ]
             
test_agConstMatch_1' =
    let exp1 = ([1,1,0],[1,1])
        exp2 = ([0,0,0],[1,0])
     in agApplySubst (fromJust $ agConstMatch exp1 exp2) exp1
            =?=
        agApplySubst (fromJust $ agConstMatch exp1 exp2) exp2
        
test_agConstMatch_2 =
    let exp1 = ([1],[1,0])
        exp2 = ([0],[0,1])
     in agConstMatch exp1 exp2
            =?=
        Just [([0],[-1,1])]
             
test_agConstMatch_2' =
    let exp1 = ([1],[1,0])
        exp2 = ([0],[0,1])
     in agApplySubst (fromJust $ agConstMatch exp1 exp2) exp1
            =?=
        agApplySubst (fromJust $ agConstMatch exp1 exp2) exp2
        
test_agConstMatch_3 =
    let exp1 = ([0],[1,0])
        exp2 = ([1],[0,1])
     in agConstMatch exp1 exp2
            =?=
        Nothing
        
test_constantify_1 =
    let exp   = (F' "f'" [X 0, X 1, X' 0, X' 1, F' "C 0" [], F' "C 1" []])
                    :: T Sig String () Int
        exp'  = (F' "f'" [C 0, X 1, X' 0, C  3, F' "C 0" [], F' "C 1" []])
                    :: T Sig String Int Int
        smv   = [X 0, X' 1] :: [T Sig String () Int]
        numC' = 0 -- numC exp
     in constantify numC' smv exp
            =?=
        exp'

test_deconstantify_1 =
    let exp   = (F' "f'" [X 0, X 1, X' 0, X' 1, F' "C 0" [], F' "C 1" []])
                    :: T Sig String () Int
        exp'  = (F' "f'" [C 0, X 1, X' 0, C  3, F' "C 0" [], F' "C 1" []])
                    :: T Sig String Int Int
        numC' = 0 -- numC exp
     in deconstantify numC' exp'
            =?=
        exp
        
test_agUnif1TreatingAsConstant_1 =
    let exp1 = (snd . head) (fromExp 5 [([2,3,-1,-4,-5],[])])
        exp2 = (snd . head) (fromExp 5 [([0,0, 0, 0, 0],[])])
        smv  = [X 4]
     in (agUnif1TreatingAsConstant smv (castC' exp1) (castC' exp2)
                :: Maybe (AGUnifProb Sig String () Int))
            =?=
        (Just $ map (castC' *** castC') $ fromExp 5 $
             [([ 1, 0, 0, 0, 0],[])
             ,([ 0, 1, 0, 0, 0],[])
             ,([ 2, 3, 0,-4,-5],[])
             ,([ 0, 0, 0, 1, 0],[])
             ,([ 0, 0, 0, 0, 1],[])])    -- this last row!

-- * AG-unification with free function symbols * --------------------------[ ]--

test_newT_1 =
    let env = [(X' 13,F' "b" [X' 1])] :: AGUnifProb Sig String String Int
     in runState (newT (F Mul [F' "a" [],X 0])) (42,env)
            =?=
        (42,(43,env ++ [(X' 42,F Mul [F' "a" [],X 0])]))

test_newV_1 =
    runState newV 42
        =?=
    (X' 42 :: T () () () (), 43)

test_isVar_1 =
    map isVar [X undefined, X' undefined, C undefined, F undefined undefined, F' undefined undefined]
        =?=
    [True, True, False, False, False]
    
test_vars_1 =
    vars (F undefined [{-C undefined,-} F' undefined [X 666, X' undefined], X 42])
        =?=
    [666,42]

test_vars'_1 =
    vars' (F undefined [{-C undefined,-} F' undefined [X' 666, X undefined], X' 42])
        =?=
    [666,42]

test_allVars_1 =
    allVars
        [(F undefined [{-C undefined,-} F' undefined [X  1, X' 2], X  3]
        ,F undefined [{-C undefined,-} F' undefined [X' 4, X  5], X' 6]
        )]
        =?=
    (S.fromList [X  1, X' 2, X  3, X' 4, X  5, X' 6] :: S.Set (T () () () Int))

test_homogeneous_1 =
    let t = F Mul [F' "f" [F' "a" []],F Mul [F' "f" [F Unit []],X "x"]]
                :: T Sig String String String
     in runState (homogeneous t) (0,[])
            =?=
        (F Mul [X' 0,F Mul [X' 1,X "x"]]
        ,(2,[(X' 0, F' "f" [F' "a" []])
            ,(X' 1, F' "f" [F Unit []])]))

test_homogeneous'_1 =
    let t = F' Mul [F "f" [F "a" []],F' Mul [F "f" [F' Unit []],X "x"]]
                 :: T String Sig String String
     in runState (homogeneous' t) (0,[])
            =?=
        (F' Mul [X' 0,F' Mul [X' 1,X "x"]]
        ,(2,[(X' 0, F "f" [F "a" []])
            ,(X' 1, F "f" [F' Unit []])]))

test_homogeneous''_1 =
    let t = F Mul [F' "f" [F' "a" []],F Mul [F' "f" [F Unit []],X "x"]]
                 :: T Sig String String String
     in runState (homogeneous'' t) 0
            =?=
        ((F Mul [X' 0,F Mul [X' 1,X "x"]]
         ,[(X' 0, F' "f" [F' "a" []])
          ,(X' 1, F' "f" [F Unit []])])
        ,2)

test_homogeneous''_2 =
    let t = F' Mul [F "f" [F "a" []],F' Mul [F "f" [F' Unit []],X "x"]]
                 :: T String Sig String String
     in runState (homogeneous'' t) 0
            =?=
        ((F' Mul [X' 0,F' Mul [X' 1,X "x"]]
         ,[(X' 0, F "f" [F "a" []])
          ,(X' 1, F "f" [F' Unit []])])
        ,2)
        
-- Example 3 (p. 454)
test_homogeneous''_3 =
    let t = F "*" [F' "f" [C "a"], F "*" [F' "f" [F "0" []], X "x"]]
     in runState (homogeneous'' t) 0
            =?=
        ((F "*" [X' 0, F "*" [X' 1, X "x"]]
         ,[(X' 0, F' "f" [C "a"])
          ,(X' 1, F' "f" [F "0" []])]
         )
        ,2)

test_isPureE =
    map isPureE
        [X undefined, X' undefined{-, C undefined-}
        ,F undefined [X undefined], F undefined [F' undefined undefined]
        ,F' undefined undefined
        ]
            =?=
    [True, True{-, True-}
    ,True, False
    ,False]

test_isPureE' =
    map isPureE'
        [X undefined, X' undefined{-, C undefined-}
        ,F undefined undefined
        ,F' undefined [X undefined], F' undefined [F undefined undefined]
        ]
            =?=
    [True, True{-, False-}
    ,False
    ,True, False]

test_isHeterogeneous_1 =
    let t = F' Mul [F' Mul [F' Unit []],F' Inv [F' Mul [F' Unit []],X "x"]]
                 :: T String Sig String String
     in isHeterogeneous t
            =?=
        False

test_isHeterogeneous_2 =
    let t = F' Mul [F "f" [F "a" []],F' Mul [F "f" [F' Unit []],X "x"]]
                 :: T String Sig String String
     in isHeterogeneous t
            =?=
        True

test_subst_1 =
    let theta = F 2 [X 2{-, C 222-}] :: T Int Int Int Int
        exp x = F 2 [F' 2 [X 1, x, X' 3{-, C 2-}], x]
     in subst 2 theta (exp (X 2))
            =?=
        exp theta

test_subst'_1 =
    let theta = F 2 [X' 2{-, C 222-}] :: T Int Int Int Int
        exp x = F 2 [F' 2 [X 1, x, X' 3{-, C 2-}], x]
     in subst' 2 theta (exp (X' 2))
            =?=
        exp theta

test_applySubst_1 =
    let theta    = F  2 [X  2, X' 2{-, C 2-}] :: T Int Int Int Int
        theta'   = F' 2 [X' 2, X  2{-, C 2-}]
        theta''  = [(X 2, theta), (X' 2, theta')]
        exp x x' = F 2 [x, F' 2 [X 1, X' 1, x', x{-, C 2-}], x']
     in applySubst theta'' (exp (X 2) (X' 2))
            =?=
        exp theta theta'

test_freeUnif_1 =
    let prob = [(X 0              , F' "f" [F' "a" []])
               ,(F' "g" [X 0, X 0], F' "g" [X 0, X 1] )]
     in freeUnif (prob :: AGUnifProb String String String Int)
            =?=
        Just [(X 0,F' "f" [F' "a" []]),(X 1,F' "f" [F' "a" []])]

test_freeUnif_2 =
    let prob = [(X 0, F' "f" [X 0])]
     in freeUnif (prob :: AGUnifProb String String String Int)
            =?=
        Nothing


-- FIXME: more tests for freeUnif (triggering each rule)

-- Example 2 (p. 453)
test_classify_1 =
    let t1  = (F "+" [X "x", F "1" []], F "0" [])
        t2  = (X "x", F "*" [X "y", X "z"])
        t3  = (F' "f" [X "x"], F "+" [X "y", X "z"])    -- gets reordered!
        t3' = (F "+" [X "y", X "z"], F' "f" [X "x"])
        t4  = (F' "f" [F "0" []], F' "f" [C "a"])
     in (fst $ classify [t1, t2, t3, t4])
            =?=
        ([t1, t2], [], [t3'], [t4])

test_classify_2 =
    let t1  = (F  "f" [X 1, X' 2, F "C 3" []],           F  "g" [X 1, X' 2, F "C 3" []]        )
        t2  = (F' "f" [X 1, X' 2     ],           F' "g" [X 1, X' 2     ]        )
        t3  = (F  "f" [X 1, X' 2, F "C 3" []],           F' "g" [X 1, X' 2     ]        )
        t3' = (F' "g" [X 1, X' 2     ],           F  "f" [X 1, X' 2, F "C 3" []]        )
        t4  = (F  "f" [F' "f'" [X 1, X' 2, F' "C 3" []]], F' "g" [F "f" [X 1, X' 2, F' "C 3" []]])
        t5  = (X 1, X' 1)
     in (fst $ classify ([t1, t2, t3, t3', t4, t5] :: AGUnifProb String String Int Int))
            =?=
        ([t1],[t2, t5],[t3, t3],[t4])

test_inSolvedForm_1 =
    let ts = [(X  1, F "f" [F' "C 1" []])
             ,(X' 1, F "f" [F' "C 1" []])
             ] :: AGUnifProb String String Int Int
        w  = dom ts
     in inSolvedForm ts
            =?=
        True

test_inSolvedForm_2 =
    let ts = [(X  1, F "f" [F' "C 1" []])
             ,(X' 1, F "f" [F' "C 1" []])
             ,(C  1, F "f" [F' "C 1" []])
             ] :: AGUnifProb String String Int Int
        w  = dom ts
     in inSolvedForm ts
            =?=
        False

test_inSolvedForm_3 =
    let ts = [(X  1, F "f" [F' "C 1" []])
             ,(X' 1, F "f" [X 1])
             ] :: AGUnifProb String String Int Int
        w  = dom ts
     in inSolvedForm ts
            =?=
        False
        
test_inSolvedForm_4 =
    let ts = [(X  1, F "f" [F' "C 1" []])
             ,(X  1, F "f" [F' "C 1" []])
             ] :: AGUnifProb String String Int Int
        w  = dom ts
     in inSolvedForm ts
            =?=
        False


test_numX =
    numX (F "f" [F' "f'" [X 42, X' 666{-, C 666-}]])
        =?=
    (42 + 1)

test_numX' =
    numX' (F "f" [F' "f'" [X 666, X' 42{-, C 666-}]])
        =?=
    (42 + 1)
    
test_numC =
    numC (F "f" [F' "f'" [X 666, X' 666, C 42]])
        =?=
    (42 + 1)

test_toExp_1 =
    toExp 2 2 0 (F Mul [F Mul [X 1, F Mul [X' 0, F Inv [X' 1]]]
                       ,F Inv [F Mul [X 0, X 0]]
                       ]
                )
        =?=
    ([-2,1,1,-1],[])

test_toExp'_1 =
    let exp = (F Mul [F Mul [X 1, F Mul [X' 0, F Inv [X' 1]]]
                     ,F Inv [F Mul [C 0, C 1]]
                     ]
              ) :: T Sig () Int Int
     in toExp' 2 2 2 (exp, exp)
            =?=
        ([0,0,0,0],[0,0])

test_fromExp_1 =
    let exp = ([1,-2,3,-4],[5,-6])
     in map (id *** toExp'' 2 2 2) (fromExp 2 (replicate 4 ([1,-2,3,-4],[5,-6])))
            =?=
        [(X 0 :: T Sig Sig Int Int, exp), (X 1, exp), (X' 0, exp), (X' 1, exp)]
            where
                toExp'' :: Int -> Int -> Int -> T Sig f' Int Int -> AGExp1
                toExp'' v1 v2 c s = toExp' v1 v2 c (s, F Unit [])

test_dom_1 =
    dom [(X 0, X 1), (X 42, X 43), (X' 0, X' 1), (X' 666, X' 667)]
        =?=
    S.fromList [X 0 :: T Sig Sig Int Int, X 42, X' 0, X' 666]

test_domNotMappingToVar_1 =
    domNotMappingToVar [(X 0, X' 0), (X 42, F Unit []), (X' 0, X 0), (X' 666, C 1)]
        =?=
    S.fromList [X 42, X' 666 :: T Sig Sig Int Int]

test_isShared_1 =
    let pe  = [(X 0, X' 1), (X' 2, X 3)] :: AGUnifProb Sig String Int Int
        pe' = [(X 0, F' "C 0" []), (F' "C 0" [], X' 1), (X 3, X' 2)]
     in map (\x -> isShared x pe pe') [X 0, X' 1, X' 2, X 3]
            =?=
        [True, True, False, False]

{-

test_agUnifN_VA_1 =
    let ph = [(X 0
              ,F Inv [F' "f'" [C 1]]
              )] :: AGUnifProb Sig String Int Int
     in runStateT (agUnifN ph) 0
            =?=
        [([(X 0,F Inv [X' 0]),(X' 0,F' "f'" [X' 1]),(X' 1,C 1)]
         ,2
         )
        ]

test_agUnifN_ERes_1 =
    let exp = ([2,3,-1,-4],[-5])
        pe  = [((snd . head) (fromExp 4 [exp])
               ,F Unit []
               )] :: AGUnifProb Sig String Int Int
     in runStateT (agUnifN pe) 42
            =?=
        [((:[]) $ (!!2) $ fromExp 4 $
             [([ 1, 0, 0, 0],[ 0])
             ,([ 0, 1, 0, 0],[ 0])
             ,([ 2, 3, 0,-4],[-5])
             ,([ 0, 0, 0, 1],[ 0])]
        ,42)
        ]

test_agUnifN_ERes_1' =
    let exp = ([2,3,-1,-4],[-5])
        pe  = [((snd . head) (fromExp 4 [exp])
               ,F Unit []
               )] :: AGUnifProb Sig String Int Int
        (unzip -> ([up], _)) = runStateT (agUnifN pe) 42
     in inSolvedForm up
            =?=
        True

test_agUnifN_E'Res_1 =
    let pe' = [(F' "f'" [F' "C0" [], X 0, X 1], F' "f'" [X 2, F' "C1" [], X 3])
              ,(F' "f'" [X 2, F' "C1" [], X 4], F' "f'" [X 5, X 6, F' "C2" []])
              ] :: AGUnifProb Sig String Int Int
     in runStateT (agUnifN pe') 42
            =?=
        [(
             [(X 0,F' "C1" [])
             ,(X 1,X 3)
             ,(X 2,F' "C0" [])
             ,(X 4,F' "C2" [])
             ,(X 5,F' "C0" [])
             ,(X 6,F' "C1" [])
         ]
        ,42
        )]

test_agUnifN_EMatch_1 =
    let pi = [(F' "f'" [X 0, X 1]
              ,F Mul [X 0, F Mul [C 0, X 1]]
              )
             ]
     in runStateT (agUnifN pi) 0
            =?=
        [(
            [(X  0,F Mul [F Inv [X 1],F Mul [X' 0,F Inv [C 0]]])
            ,(X' 0,F' "f'" [X 0,X 1])]
        ,1
        )]
        
-- p. 458
test_agUnifN_MergeEMatch_1 =
    let p = [(X 0, F' "f" [C 0])
            ,(X 1, F' "f" [C 1])
            ,(X 0, F Mul [X 1, X 2])
            ]
     in runStateT (agUnifN p) 0
            =?=
        [(
            [(X' 0,C 0)
            ,(X' 1,C 1)
            ,(X  2,F Mul [X 0,F Inv [X 1]])
            ,(X  0,F' "f" [X' 0])
            ,(X  1,F' "f" [X' 1])
            ]
        ,2
        )]

test_agUnifN_VarRep_1 =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X 3, X 4)] ++ notShared (X 3) ++ shared (X 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 4) ++ notShared (X 4))
        
test_agUnifN_VarRep_1' =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X 4, X 3)] ++ notShared (X 3) ++ shared (X 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 4) ++ notShared (X 4))
        
test_agUnifN_VarRep_1'' =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X 3, X' 4)] ++ notShared (X 3) ++ shared (X' 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X' 4) ++ notShared (X' 4))
        
test_agUnifN_VarRep_1''' =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X' 3, X 4)] ++ notShared (X' 3) ++ shared (X 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 4) ++ notShared (X 4))

test_agUnifN_VarRep_2 =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X 3, X 4)] ++ shared (X 3) ++ notShared (X 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 3) ++ notShared (X 3))

test_agUnifN_VarRep_2' =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X 4, X 3)] ++ shared (X 3) ++ notShared (X 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 3) ++ notShared (X 3))

test_agUnifN_VarRep_2'' =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X 4, X' 3)] ++ shared (X' 3) ++ notShared (X 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X' 3) ++ notShared (X' 3))

test_agUnifN_VarRep_2''' =
    let shared    x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        notShared x = [(X 2, F Inv [x])]
        p           = [(X' 4, X 3)] ++ shared (X 3) ++ notShared (X' 4)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 3) ++ notShared (X 3))

test_agUnifN_VarRep_3 =
    let notShared  x = [(X 0, F  Inv  [x])]
        notShared' x = [(X 1, F' "f'" [x])]
        p            = [(X 2, X 3)] ++ notShared (X 2) ++ notShared' (X 3)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (notShared (X 3) ++ notShared' (X 3))
        
test_agUnifN_VarRep_3' =
    let notShared  x = [(X 0, F  Inv  [x])]
        notShared' x = [(X 1, F' "f'" [x])]
        p            = [(X 3, X 2)] ++ notShared (X 2) ++ notShared' (X 3)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (notShared (X 2) ++ notShared' (X 2))

test_agUnifN_VarRep_3'' =
    let notShared  x = [(X 0, F  Inv  [x])]
        notShared' x = [(X 1, F' "f'" [x])]
        p            = [(X 2, X' 3)] ++ notShared (X 2) ++ notShared' (X' 3)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (notShared (X' 3) ++ notShared' (X' 3))
        
test_agUnifN_VarRep_3''' =
    let notShared  x = [(X 0, F  Inv  [x])]
        notShared' x = [(X 1, F' "f'" [x])]
        p            = [(X' 2, X 3)] ++ notShared (X' 2) ++ notShared' (X 3)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (notShared (X 3) ++ notShared' (X 3))
        
test_agUnifN_VarRep_4 =
    let shared  x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        shared' x = [(X 2, F' "f'" [x]), (X 3, F Inv [x])]
        p         = [(X 4, X 5)] ++ shared (X 4) ++ shared' (X 5)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 5) ++ shared' (X 5))
        
test_agUnifN_VarRep_4' =
    let shared  x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        shared' x = [(X 2, F' "f'" [x]), (X 3, F Inv [x])]
        p         = [(X 5, X 4)] ++ shared (X 4) ++ shared' (X 5)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 4) ++ shared' (X 4))
        
test_agUnifN_VarRep_4'' =
    let shared  x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        shared' x = [(X 2, F' "f'" [x]), (X 3, F Inv [x])]
        p         = [(X 4, X' 5)] ++ shared (X 4) ++ shared' (X' 5)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X' 5) ++ shared' (X' 5))
        
test_agUnifN_VarRep_4''' =
    let shared  x = [(X 0, F Inv [x]), (X 1, F' "f'" [x])]
        shared' x = [(X 2, F' "f'" [x]), (X 3, F Inv [x])]
        p         = [(X' 4, X 5)] ++ shared (X' 4) ++ shared' (X 5)
                            :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        (shared (X 5) ++ shared' (X 5))
        
test_agUnifN_VarRep_5 =
    let p = [(X 0, X 1), (X 2, F Inv [X 0])]
                :: AGUnifProb Sig String Int Int
        (unzip -> ([sortBy (compare `on` fst) -> p'], (all (==0) -> True)))
            = runStateT (agUnifN p) 0
     in p'
            =?=
        p

-}

-- should have 2! = 2 unique solutions (Liu & Lynch)
test_agUnifN_1 =
    let p = [(F Mul [F' "f" [X 0], F' "f" [X 1]]
             ,F Mul [F' "f" [F' "c_0" []], F' "f" [F' "c_1" []]])]
                :: AGUnifProb Sig String () Int
        w   = allVars p

        {-
        (nub . (map (sortBy (compare `on` fst) *** id)) -> ps')
            = runStateT (agUnifN' p) (0, [LE START (fst $ classify p)])
        -}
        ps' = agUnifN p

     in ps'
            =?=
        [[(X 0,F' "c_0" []),(X 1,F' "c_1" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_0" [])]]


test_agUnifN_1B =
    let p = [(F Mul [F' "f" [F' "c_1" []], F' "f" [F' "c_1" []]]
             ,F Mul [F' "f" [F' "c_0" []], F' "f" [F' "c_1" []]])]
                :: AGUnifProb Sig String () Int
        w   = allVars p

        {-
        (nub . (map (sortBy (compare `on` fst) *** id)) -> ps')
            = runStateT (agUnifN' p) (0, [LE START (fst $ classify p)])
        -}
        ps' = agUnifN p

     in ps'
            =?=
        []

-- should have 3! = 6 unique solutions (Liu & Lynch)
test_agUnifN_2 =
    let p = [(F Mul [F' "f" [X 0], F Mul [F' "f" [X 1], F' "f" [X 2]]]
             ,F Mul [F' "f" [F' "c_0" []], F Mul [F' "f" [F' "c_1" []], F' "f" [F' "c_2" []]]])]
                :: AGUnifProb Sig String () Int
        w   = allVars p

        {-
        (nub . (map (sortBy (compare `on` fst) *** id)) -> ps')
            = runStateT (agUnifN' p) (0, [LE START (fst $ classify p)])
        -}
        ps' = agUnifN p

     in ps'
            =?=
        [[(X 0,F' "c_0" []),(X 1,F' "c_1" []),(X 2,F' "c_2" [])]
        ,[(X 0,F' "c_0" []),(X 1,F' "c_2" []),(X 2,F' "c_1" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_0" []),(X 2,F' "c_2" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_2" []),(X 2,F' "c_0" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_0" []),(X 2,F' "c_1" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_1" []),(X 2,F' "c_0" [])]]
        
-- should have 4! = 24 unique solutions (Liu & Lynch)
test_agUnifN_3 =
    let p = [(F Mul [F' "f" [X 0], F Mul [F' "f" [X 1], F Mul [F' "f" [X 2], F' "f" [X 3]]]]
             ,F Mul [F' "f" [F' "c_0" []], F Mul [F' "f" [F' "c_1" []], F Mul [F' "f" [F' "c_2" []], F' "f" [F' "c_3" []]]]])]
                :: AGUnifProb Sig String () Int
        w   = allVars p

        {-
        (nub . (map (sortBy (compare `on` fst) *** id)) -> ps')
            = runStateT (agUnifN' p) (0, [LE START (fst $ classify p)])
        -}
        ps' = agUnifN p

     in ps'
            =?=
        [[(X 0,F' "c_0" []),(X 1,F' "c_1" []),(X 2,F' "c_2" []),(X 3,F' "c_3" [])]
        ,[(X 0,F' "c_0" []),(X 1,F' "c_1" []),(X 2,F' "c_3" []),(X 3,F' "c_2" [])]
        ,[(X 0,F' "c_0" []),(X 1,F' "c_2" []),(X 2,F' "c_1" []),(X 3,F' "c_3" [])]
        ,[(X 0,F' "c_0" []),(X 1,F' "c_2" []),(X 2,F' "c_3" []),(X 3,F' "c_1" [])]
        ,[(X 0,F' "c_0" []),(X 1,F' "c_3" []),(X 2,F' "c_1" []),(X 3,F' "c_2" [])]
        ,[(X 0,F' "c_0" []),(X 1,F' "c_3" []),(X 2,F' "c_2" []),(X 3,F' "c_1" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_0" []),(X 2,F' "c_2" []),(X 3,F' "c_3" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_0" []),(X 2,F' "c_3" []),(X 3,F' "c_2" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_2" []),(X 2,F' "c_0" []),(X 3,F' "c_3" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_2" []),(X 2,F' "c_3" []),(X 3,F' "c_0" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_3" []),(X 2,F' "c_0" []),(X 3,F' "c_2" [])]
        ,[(X 0,F' "c_1" []),(X 1,F' "c_3" []),(X 2,F' "c_2" []),(X 3,F' "c_0" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_0" []),(X 2,F' "c_1" []),(X 3,F' "c_3" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_0" []),(X 2,F' "c_3" []),(X 3,F' "c_1" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_1" []),(X 2,F' "c_0" []),(X 3,F' "c_3" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_1" []),(X 2,F' "c_3" []),(X 3,F' "c_0" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_3" []),(X 2,F' "c_0" []),(X 3,F' "c_1" [])]
        ,[(X 0,F' "c_2" []),(X 1,F' "c_3" []),(X 2,F' "c_1" []),(X 3,F' "c_0" [])]
        ,[(X 0,F' "c_3" []),(X 1,F' "c_0" []),(X 2,F' "c_1" []),(X 3,F' "c_2" [])]
        ,[(X 0,F' "c_3" []),(X 1,F' "c_0" []),(X 2,F' "c_2" []),(X 3,F' "c_1" [])]
        ,[(X 0,F' "c_3" []),(X 1,F' "c_1" []),(X 2,F' "c_0" []),(X 3,F' "c_2" [])]
        ,[(X 0,F' "c_3" []),(X 1,F' "c_1" []),(X 2,F' "c_2" []),(X 3,F' "c_0" [])]
        ,[(X 0,F' "c_3" []),(X 1,F' "c_2" []),(X 2,F' "c_0" []),(X 3,F' "c_1" [])]
        ,[(X 0,F' "c_3" []),(X 1,F' "c_2" []),(X 2,F' "c_1" []),(X 3,F' "c_0" [])]]

-- x = f ( x + y ) should have 1 solution (Liu & Lynch) (WHICH???)
test_agUnifN_4 =
    let p = [(X 0
             ,F' "f" [F Mul [X 0, X 1]]
            )] :: AGUnifProb Sig String () Int
     in runStateT (agUnifN' p) (0,[])
{-            =?=
-}

-- x + f ( y ) − f ( x1 ) = ? 0
-- y + f ( z ) − f ( x2 ) = ? 0  should have 3 solutions  (Liu & Lynch)
-- z + f ( x ) − f ( x3 ) = ? 0
test_agUnifN_5 =
    let x  = X 0
        y  = X 1
        z  = X 2
        x1 = X 3
        x2 = X 4
        x3 = X 5
        p = [(F Mul [x, F Mul [F' "f" [y], F Inv [F' "f" [x1]]]],F Unit [])
            ,(F Mul [y, F Mul [F' "f" [z], F Inv [F' "f" [x2]]]],F Unit [])
            ,(F Mul [z, F Mul [F' "f" [x], F Inv [F' "f" [x3]]]],F Unit [])
            ] :: AGUnifProb Sig String () Int
     in runStateT (agUnifN' p) (0,[])
