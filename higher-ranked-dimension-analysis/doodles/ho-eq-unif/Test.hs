module Test where

import Control.Monad
import Control.Monad.State

import qualified Data.Set as S

import Main

tests :: [(String, Bool)]
tests =
    [("for",            test_for)
    ,("statefulForM 1", test_statefulForM_1)
    ,("statefulForM 2", test_statefulForM_2)
    ,("(!!!)",          test_III)
    ,("unionMap",       test_unionMap)
    ,("unionMap'",      test_unionMap')
    ,("base",           test_base)
    ,("sig2ty",         test_sig2ty)
    ,("sparsifySubst",  test_sparsifySubst)
    ,("unFreeV",        test_unFreeV)
    ,("isBound",        test_isBound)
    ,("isFreeV",        test_isFreeV)
    ,("isFreeC",        test_isFreeC)
    ,("isConst",        test_isConst)
    ,("freeV",          test_freeV)
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

-- * Types * --------------------------------------------------------------[ ]--

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
    map isBound [Bound 9, FreeV 9, FreeC 9, Const Mul] =?= [True, False, False, False]
test_isFreeV = 
    map isFreeV [Bound 9, FreeV 9, FreeC 9, Const Mul] =?= [False, True, False, False]
test_isFreeC = 
    map isFreeC [Bound 9, FreeV 9, FreeC 9, Const Mul] =?= [False, False, True, False]
test_isConst = 
    map isConst [Bound 9, FreeV 9, FreeC 9, Const Mul] =?= [False, False, False, True]

test_freeV =
    let
        ty  n = replicate n (base Real) :-> Real
        env   = map ty [0..]
    in
        (freeV env 2 :: AlgebraicTerm Sort Sig)
            =?=
        A [base Real, base Real] (FreeV 2) [A [] (Bound 0) [], A [] (Bound 1) []]








