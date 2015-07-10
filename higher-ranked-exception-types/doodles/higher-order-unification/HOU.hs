{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.Char
import Data.List

-- Types

type Idx = Int

data Name
    = Free  Idx
    | Bound Idx
    | Con   Idx
    deriving (Eq, Read)
    
instance Show Name where
    show (Free  x) | x <= 26   = [chr $ ord 'a' + x - 1]
                   | otherwise = "?" ++ show x
    show (Bound x) = show x
    show (Con   x) = [chr $ ord 'A' + x - 1]

data Ty
    = Base Idx
    | Arr  Ty Ty
    deriving (Eq, Read, Show)

data Ty' 
    = Arr'  [Ty'] Idx
    deriving (Eq, Read)

base' :: Idx -> Ty'
base' b = Arr' [] b

instance Show Ty' where
    show (Arr' _ t) = "T"       -- FIXME

arity :: Ty' -> Int
arity (Arr' as b) = length as

args :: Ty' -> [Ty']
args (Arr' as b) = as

data Tm
    = Var Name
    | Abs Ty Tm
    | App Tm Tm
    deriving (Eq, Read, Show)

data Nf'
    = Nf' [Ty'] Name [Nf']
    deriving (Eq, Read)
    
instance Show Nf' where
    show (Nf' ts f xs) = concatMap (\t -> "\\" ++ show t ++ ".") ts ++ show f ++ (if null xs then "" else "(" ++ intercalate "," (map show xs) ++ ")")
    
heading :: Nf' -> Name
heading (Nf' _ x _) = x
    
rigid :: Nf' -> Bool
rigid (Nf' _ (Free  _) _) = False
rigid (Nf' _ (Bound _) _) = True
rigid (Nf' _ (Con   _) _) = True

constant :: Nf' -> Bool
constant (Nf' _ (Free  _) _) = False
constant (Nf' _ (Bound _) _) = False
constant (Nf' _ (Con   _) _) = True


-- Huet's higher-order unification algorithm

type DisagreementSet  = [(Nf',Nf')]
type SubstitutionPair = (Idx, Tm)

data MatchingTree
    = S
    | F
    | Node DisagreementSet [(SubstitutionPair, MatchingTree)]
    deriving Show

-- * Simplification

simpl :: DisagreementSet -> MatchingTree
simpl n = case step1 n of
            Nothing                -> F
            Just (map step2 -> n') ->
                if any (rigid . snd) n' then Node n' [] else S
    where step2 (e1, e2) | rigid e1 && not (rigid e2) = (e2, e1)
                         | otherwise                  = (e1, e2)

step1 :: DisagreementSet -> Maybe DisagreementSet
step1 = step1' [] where
    step1' :: DisagreementSet -> DisagreementSet -> Maybe DisagreementSet
    step1' xs []     = Just (nub xs)
    step1' xs (e@(e1,e2):es)
        | rigid e1 && rigid e2 = do
            es' <- f e
            step1' xs (nub (es ++ es'))
        | otherwise = do
            step1' (e:xs) es
    f :: (Nf',Nf') -> Maybe DisagreementSet
    f (Nf' ts1 f1 xs1, Nf' ts2 f2 xs2)
            = if f1 == f2 then
                Just $ zipWith (\(Nf' ts1' f1' xs1') (Nf' ts2' f2' xs2') -> (Nf' (ts1 ++ ts1') f1' xs1', Nf' (ts2 ++ ts2') f2' xs2')) xs1 xs2
              else
                Nothing
                     
ex1 = [(Nf' [] (Con 1) [Nf' [base' 0] (Con 2) [Nf' [] (Free 24) [], Nf' [] (Bound 0) []],Nf' [] (Con 3) []], Nf' [] (Con 1) [Nf' [base' 0] (Con 2) [Nf' [] (Free 25) [], Nf' [] (Bound 0) []],Nf' [] (Free 6) [Nf' [] (Con 3) []]])] {- Node [(\T0.x,\T0.y),(f(C),C)] [] -}
ex2 = [(Nf' [] (Con 1) [Nf' [base' 0] (Con 2) [Nf' [] (Free 24) [], Nf' [] (Bound 0) []]], Nf' [] (Con 1) [Nf' [base' 0] (Con 2) [Nf' [] (Free 25) [], Nf' [] (Bound 0) []]])] {- S -}
ex3 = [(Nf' [base' 0, base' 0] (Con 1) [Nf' [] (Bound 1) [], Nf' [base' 0] (Bound 1) []], Nf' [base' 0, base' 0] (Con 1) [Nf' [] (Bound 1) [], Nf' [base' 0] (Bound 2) []])] {- F -}

-- * Matching

type Env     = [Ty']
type Unifier = (Idx, Nf')

match :: Env -> Nf' -> Nf' -> Idx -> [Unifier]
match env (Nf' us (Free f) e1s) e2@(Nf' vs r e2s) v
    | length us > length vs = error "length us > length vs"
    | otherwise = 
        let n1 = length us
            n2 = length vs
            n  = n2 - n1            -- eta: n1 = n2 => n = 0
            p1 = length e1s
            p2 = length e2s
            ws = args (env !! (f-1))
            -- imitation
            sI = if constant e2 then
                    [(f, Nf' ws r (map (\x -> Nf' [] (Free (v+x)) (map (\y -> Nf' [] (Bound y) []) (reverse [0..p1-1]))) [1..p2]))]
                 else
                    []
            -- projection
            sP = [ (f, Nf' ws (Bound i) (map (\x -> Nf' [] (Free (v+x)) (map (\y -> Nf' [] (Bound y) []) (reverse [0..p1-1]))) [1..arity t]))
                 | (i,t) <- zip (reverse [0..p1-1]) ws
                 ]
         in nub (sI ++ sP)
         
mEx1 = match (replicate 5 undefined
                ++ [Arr' [Arr' [base' 3, base' 3] 3, base' 3] 3]
                ++ replicate 17 undefined
                ++ [Arr' [base' 3, base' 3] 3])
             (Nf' [] (Free 6) [Nf' [] (Free 24) [], Nf' [] (Con 2) []])
             (Nf' [] (Con 1) [Nf' [] (Con 2) []]) 100
