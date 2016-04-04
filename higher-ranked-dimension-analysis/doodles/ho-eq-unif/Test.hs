{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Test where

import Control.Monad
import Control.Monad.State

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Main hiding (u0)

tests :: [(String, Bool)]
tests =
    [("for",                            test_for)
    ,("statefulForM (1)",               test_statefulForM_1)
    ,("statefulForM (2)",               test_statefulForM_2)
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

-- | Utility | ------------------------------------------------------------[X]--

test_for = for [0..9] (*2) == map (*2) [0..9]

test_statefulForM_1 = statefulForM (0::Int) [0..10] f =?= Just (11, [0,2..20])
    where f t x = return (t + 1, x + t)

test_statefulForM_2 = statefulForM (0::Int) [10,9..0] f =?= Nothing
    where f t x = if x - t > 0 then
                    return (t + 1, x - t)
                  else
                    fail "negative"
                    
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

-- * Maximal flexible subterms (Qian & Wang) * ----------------------------[ ]--

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
            


-- * Transformation rules (Qian & Wang) * ---------------------------------[ ]--

-- \x.F(x) =?= \x.F(x)*G(x)*x
--         === \x.*(F(x),*(G(x),x))
test_transformAbs_1 =
    let subst      = []   -- needs to be as long as envV?
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
        
test_transformAbs_1' = snd . fromJust . fst $ test_transformAbs_1













