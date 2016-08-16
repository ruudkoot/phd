{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.AbelianGroups (
    AG(..),
    agUnif1',
    agUnif1TreatingAsConstant,
    agConstMatch,
    toExp,                      -- FIXME
    toExp',                     -- FIXME
    fromExp,                    -- FIXME
    _tests_
) where

import Control.Arrow         ((***))
import Data.Function         (on)
import Data.List             (minimumBy)
import Data.Maybe            (fromJust)

import Unif.FirstOrder.Types

import Test.Util

-- * AG-unification with free nullary constants (unitary) * ---------------[X]--

-- Kennedy (1996) / Lankford, Butler & Brady (1984) + Knuth (1969)

data AG
    = Mul
    | Inv
    | Unit
  deriving (Eq, Bounded, Enum, Ord, Show)
  -- FIXME: arbitrary Ord for Set

count p = length . filter p

set :: [a] -> Int -> a -> [a]
set xs n x = let (xs1,_:xs2) = splitAt n xs in xs1 ++ [x] ++ xs2

divides :: Integral a => a -> a -> Bool
x `divides` y = y `mod` x == 0

type AGExp1   = ([Int],[Int])
type AGSubst1 = [AGExp1]

agIdSubst :: Int -> Int -> AGSubst1
agIdSubst m' n' = map idRow [0 .. m' - 1]
  where idRow x = (replicate x 0 ++ [1] ++ replicate (m' - x - 1) 0, replicate n' 0)

-- matrix-vector multiplication
agApplySubst :: AGSubst1 -> AGExp1 -> AGExp1
agApplySubst ss (ds@(length -> m'),bs) | length ss == m'
    = foldr f (replicate m' 0, bs) (zip ss ds)
        where f ((ds',bs'),d) (ds'',bs'')
                = (zipWith (\d' d'' -> d * d' + d'') ds' ds''
                  ,zipWith (\b' b'' -> d * b' + b'') bs' bs'')

-- matrix-matrix multiplication
agCompSubst :: AGSubst1 -> AGSubst1 -> AGSubst1
agCompSubst ss us = map (agApplySubst ss) us

-- FIXME: verify solution is valid
agUnif1 :: AGExp1 -> Maybe AGSubst1
agUnif1 delta@(xs@(length -> m'), ys@(length -> n')) =
    let m     = count (/= 0) xs
        n     = count (/= 0) ys
        (d,x) = minimumBy (compare `on` (abs . snd)) (filter ((/= 0) . snd) (zip [0..] xs))
     in case (m,n) of
            (0,0) -> Just (agIdSubst m' n')
            (0,_) -> Nothing
            (1,_) | all (x `divides`) ys -> Just $
                      set (agIdSubst m' n') d (replicate m' 0, map (\y -> -y `div` x) ys)
                  | otherwise            -> Nothing
            (_,_) -> do
                -- 'div' always rounds down (also for a negative lhs)
                let us = set (agIdSubst m' n') d
                             (set (map (\x' -> -(x' `div` x)) xs) d 1
                             ,     map (\y  -> -(y  `div` x)) ys     )
                ss <- agUnif1 (agApplySubst us delta)
                return $ agCompSubst ss us

-- solve a system of equations
-- FIXME: verify solution is valid
agUnif1' :: [AGExp1] -> Maybe AGSubst1
agUnif1' [x]    = agUnif1 x
agUnif1' (x:xs) = do s <- agUnif1 x
                     t <- agUnif1' (map (agApplySubst s) xs)
                     return $ agCompSubst t s

-- solve the constant matching problem
-- FIXME: verify solution is valid
agConstMatch :: AGExp1 -> AGExp1 -> Maybe AGSubst1
agConstMatch (vs1@(length -> m ), cs1@(length -> n ))
             (vs2@(length -> m'), cs2@(length -> n'))
  | m == m' && n == n'
    = let vs = vs1
          cs = zipWith (\c1 c2 -> c1 - c2) (cs1 ++ replicate m 0) (cs2 ++ vs2)
       in case agUnif1 (vs, cs) of
            Nothing    -> Nothing
            Just subst -> Just (map f subst)
                where f (vs, splitAt n -> (cs, cs')) = (zipWith (+) vs cs', cs)
  | otherwise = error "agConstMatch: m /= m' || n /= n'"

-- Solve a system of equations in AG, while treating a set of given variables as
-- constants.
agUnif1TreatingAsConstant
    :: TermAlg AG f' () Int
    => [T AG f' () Int]               -- set of marked variables SMV
    -> FOUnifProb AG f' () Int
    -> Maybe (FOUnifProb AG f' () Int)
agUnif1TreatingAsConstant smv p
    = let numV1  = maximum (map (\(s,t) -> max (numX  s) (numX  t)) p)
          numV2  = maximum (map (\(s,t) -> max (numX' s) (numX' t)) p)
          numC'  = 0 -- max (numC  s) (numC  t)
          p'     = map (constantify numC'  smv *** constantify numC' smv) p
          numC'' = maximum (map (\(s,t) -> max (numC  s) (numC  t)) p')
       in case agUnif1' (map (toExp' numV1 numV2 numC'') p') of
            Nothing -> Nothing
            Just agSubst -> Just $ map (deconstantify numC' *** deconstantify numC')
                                       (fromExp numV1 agSubst)
       
constantify
    :: TermAlg AG f' Int Int
    => Int
    -> [T AG f' () Int]
    -> T AG f' () Int
    -> T AG f' Int Int
constantify numC' smv = constantify'
  where
    constantify' (X  x    ) | X  x  `elem` smv = C (numC' + 2 * x)
                            | otherwise        = X x
    constantify' (X' x'   ) | X' x' `elem` smv = C (numC' + 2 * x' + 1)
                            | otherwise        = X' x'
    constantify' (C  c    ) = error "constantify'" -- C  c
    constantify' (F  f  ts) = F  f  (map constantify' ts)
    constantify' (F' f' ts) = F' f' (map constantify' ts)
    
deconstantify
    :: TermAlg AG f' Int Int
    => Int
    -> T AG f' Int Int
    -> T AG f' () Int
deconstantify numC' = deconstantify'
  where
    deconstantify' (X  x ) = X  x
    deconstantify' (X' x') = X' x'
    deconstantify' (C  c ) | c < numC'                        = error "deconstantify'"
                                                           -- = C  c
                           | (x ,0) <- (c - numC') `divMod` 2 = X  x
                           | (x',1) <- (c - numC') `divMod` 2 = X' x'
    deconstantify' (F  f  ts) = F  f  (map deconstantify' ts)
    deconstantify' (F' f' ts) = F' f' (map deconstantify' ts)
    
    
-------------------------------------------------------------------------------

toExp :: Int -> Int -> Int -> T AG f' () Int -> AGExp1
toExp v1 v2 c s = toExp' v1 v2 c (castC s, F Unit [])

toExp' :: Int -> Int -> Int -> (T AG f' Int Int, T AG f' Int Int) -> AGExp1
toExp' v1 v2 c (s,t) = mul (toExp'' s) (inv (toExp'' t))
  where
    toExp'' (X  x           ) = let (vs,cs) = unit in (set vs       x   1, cs)
    toExp'' (X' x'          ) = let (vs,cs) = unit in (set vs (v1 + x') 1, cs)
    toExp'' (C  c           ) = let (vs,cs) = unit in (vs, set cs c 1)
    toExp'' (F  Unit [     ]) = unit
    toExp'' (F  Inv  [t    ]) = inv (toExp'' t)
    toExp'' (F  Mul  [t1,t2]) = mul (toExp'' t1) (toExp'' t2)

    unit = (replicate (v1 + v2) 0, replicate c 0)
    inv  = map negate *** map negate
    mul (xs,xs') (ys,ys') = (zipWith (+) xs ys, zipWith (+) xs' ys')
    

fromExp :: Int -> AGSubst1 -> FOUnifProb AG f' Int Int
fromExp v1 ss@(length -> v)
    = zipWith (\x t -> (x, fromExp' t)) (map X [0 .. v1 - 1] ++ map X' [0 .. v - v1]) ss
  where
    fromExp' :: AGExp1 -> T AG f' Int Int
    fromExp' (splitAt v1 -> (vs,vs'),cs)
        = let xs =    map (fromExp'' X ) (filter ((/=0) . snd) (zip [0 .. v1]     vs ))
                   ++ map (fromExp'' X') (filter ((/=0) . snd) (zip [0 .. v - v1] vs'))
                   ++ map (fromExp'' C ) (filter ((/=0) . snd) (zip [0 .. ]       cs ))
           in case xs of
                [] -> F Unit []
                _  -> foldr1 (\x y -> F Mul [x,y]) xs

    fromExp'' :: (Int -> T AG f' Int Int) -> (Int, Int) -> T AG f' Int Int
    fromExp'' con (x,n)
        | n < 0     = F Inv [fromExp'' con (x,-n)]
        | otherwise = foldr1 (\_ y -> F Mul [con x,y]) (replicate n (con x))


-- | TESTS | -------------------------------------------------------------------

_tests_ :: [(String,Bool)]
_tests_ = 
    [("count (1)",                      test_count_1)
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
    ,("constantify (1)",                test_constantify_1)
    ,("deconstantify (1)",              test_deconstantify_1)
    ,("agUnif1TreatingAsConstant (1)",  test_agUnif1TreatingAsConstant_1)
    ,("toExp (1)",                      test_toExp_1)
    ,("toExp' (1)",                     test_toExp'_1)
    ,("fromExp (1)",                    test_fromExp_1)
    ]
    
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
                    :: T AG String () Int
        exp'  = (F' "f'" [C 0, X 1, X' 0, C  3, F' "C 0" [], F' "C 1" []])
                    :: T AG String Int Int
        smv   = [X 0, X' 1] :: [T AG String () Int]
        numC' = 0 -- numC exp
     in constantify numC' smv exp
            =?=
        exp'

test_deconstantify_1 =
    let exp   = (F' "f'" [X 0, X 1, X' 0, X' 1, F' "C 0" [], F' "C 1" []])
                    :: T AG String () Int
        exp'  = (F' "f'" [C 0, X 1, X' 0, C  3, F' "C 0" [], F' "C 1" []])
                    :: T AG String Int Int
        numC' = 0 -- numC exp
     in deconstantify numC' exp'
            =?=
        exp
        
test_agUnif1TreatingAsConstant_1 =
    let exp1 = (snd . head) (fromExp 5 [([2,3,-1,-4,-5],[])])
        exp2 = (snd . head) (fromExp 5 [([0,0, 0, 0, 0],[])])
        smv  = [X 4]
     in (agUnif1TreatingAsConstant smv [(castC' exp1, castC' exp2)]
                :: Maybe (FOUnifProb AG String () Int))
            =?=
        (Just $ map (castC' *** castC') $ fromExp 5 $
             [([ 1, 0, 0, 0, 0],[])
             ,([ 0, 1, 0, 0, 0],[])
             ,([ 2, 3, 0,-4,-5],[])
             ,([ 0, 0, 0, 1, 0],[])
             ,([ 0, 0, 0, 0, 1],[])])    -- this last row!
             
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
              ) :: T AG () Int Int
     in toExp' 2 2 2 (exp, exp)
            =?=
        ([0,0,0,0],[0,0])

test_fromExp_1 =
    let exp = ([1,-2,3,-4],[5,-6])
     in map (id *** toExp'' 2 2 2) (fromExp 2 (replicate 4 ([1,-2,3,-4],[5,-6])))
            =?=
        [(X 0 :: T AG AG Int Int, exp), (X 1, exp), (X' 0, exp), (X' 1, exp)]
            where
                toExp'' :: Int -> Int -> Int -> T AG f' Int Int -> AGExp1
                toExp'' v1 v2 c s = toExp' v1 v2 c (s, F Unit [])
