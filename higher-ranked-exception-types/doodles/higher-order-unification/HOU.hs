{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Monad

import Data.Char
import Data.List

-- | The 'concatMapM' function generalizes 'concatMap' to arbitrary monads.
concatMapM        :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs   =  liftM concat (mapM f xs)

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
    = Base' Idx
    | Arr'  [Ty'] Idx
    | Unknown
    deriving (Eq, Read)
    
instance Show Ty' where
    show (Base' t) = "T" ++ show t
    show (Unknown) = "?"

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
                     
ex1 = [(Nf' [] (Con 1) [Nf' [Base' 0] (Con 2) [Nf' [] (Free 24) [], Nf' [] (Bound 0) []],Nf' [] (Con 3) []], Nf' [] (Con 1) [Nf' [Base' 0] (Con 2) [Nf' [] (Free 25) [], Nf' [] (Bound 0) []],Nf' [] (Free 6) [Nf' [] (Con 3) []]])] {- Node [(\T0.x,\T0.y),(f(C),C)] [] -}
ex2 = [(Nf' [] (Con 1) [Nf' [Base' 0] (Con 2) [Nf' [] (Free 24) [], Nf' [] (Bound 0) []]], Nf' [] (Con 1) [Nf' [Base' 0] (Con 2) [Nf' [] (Free 25) [], Nf' [] (Bound 0) []]])] {- S -}
ex3 = [(Nf' [Base' 0, Base' 0] (Con 1) [Nf' [] (Bound 1) [], Nf' [Base' 0] (Bound 1) []], Nf' [Base' 0, Base' 0] (Con 1) [Nf' [] (Bound 1) [], Nf' [Base' 0] (Bound 2) []])] {- F -}

-- * Matching

type Unifier = (Idx, Nf')

match :: Nf' -> Nf' -> Idx -> [Unifier]
match (Nf' us (Free f) e1s) e2@(Nf' vs r e2s) v
    | length us > length vs = error "length us > length vs"
    | otherwise = 
        let n1 = length us
            n2 = length vs
            n  = n2 - n1            -- eta: n1 = n2 => n = 0
            p1 = length e1s
            p2 = length e2s
            ws = replicate p1 Unknown
            -- imitation
            sI = if constant e2 then
                    [(f, Nf' ws r (map (\x -> Nf' [] (Free (v+x)) (map (\y -> Nf' [] (Bound y) []) [p1-1..0])) [1..p2]))]
                 else
                    []
            -- projection
            -- FIXME: we do not check the typing condition (2) yet
            sP = [ (f, Nf' ws (Bound i) (map (\x -> Nf' [] (Free (v+x)) (map (\y -> Nf' [] (Bound y) []) [p1-1..0])) [1..p2]))
                 | i <- [p1-1..0]
                 ]
         in sI ++ sP
         
mEx1 = match (Nf' [] (Free 6) [Nf' [] (Free 24) [], Nf' [] (Con 2) []])
             (Nf' [] (Con 1) [Nf' [] (Con 2) []]) 100
