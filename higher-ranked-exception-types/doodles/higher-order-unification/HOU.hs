{-# LANGUAGE TupleSections, ViewPatterns #-}

module Main where

import Control.Applicative ((<$>))
import Control.Arrow       ((***))

import           Data.Char
import           Data.List
import qualified Data.Tree as T

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

data Tm'
    = Tm' [Ty'] (Either Name Tm') [Tm']
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
type SubstitutionPair = (Idx, Nf')

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

match :: Env -> Nf' -> Nf' -> Idx -> [SubstitutionPair]
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
             
-- * Matching trees

matchingTree :: Env -> [Nf'] -> MatchingTree
matchingTree env es = head (matchingTrees env es)

matchingTrees :: Env -> [Nf'] -> [MatchingTree]
matchingTrees env (e0:es) = matchingTrees' $ simpl (map (e0,) es) where
    matchingTrees' :: MatchingTree -> [MatchingTree]
    matchingTrees' S            = return S
    matchingTrees' F            = return F
    matchingTrees' (Node ds []) = do
        (e1,e2) <- filter (rigid . snd) ds
        case match env e1 e2 (length env) of
            []     -> return F
            sigmas -> Node ds <$> map f sigmas where
                f sigma = do
                    let ds' = map (applySubst sigma *** applySubst sigma) ds
                    m <- matchingTrees' (simpl ds')
                    return (sigma, m)
                    
-- Example 3.2

-- * Substitution and beta-reduction

nf2tm :: Nf' -> Tm'
nf2tm (Nf' bs x as) = Tm' bs (Left x) (map nf2tm as)

tm2nf :: Tm' -> Nf'
tm2nf (Tm' bs (Left x) as) = Nf' bs x (map tm2nf as)

normalize :: Tm' -> Tm'
normalize (Tm' xs (Left f) ts)
    = Tm' xs (Left f) (map normalize ts)
normalize (Tm' xs (Right (Tm' ys f ss)) ts)
    = let n = length ys
          q = length ts
       in if q <= n then    -- FIXME: recurse
            Tm' (xs ++ drop q ys) (bind (n-q) ts f) (map (bindR (n-q) ts) ss)
          else
            error "normalize: not eta-long?"

maxBoundIndex :: [Tm'] -> Idx
maxBoundIndex ts = maximum (0 : map maxBoundIndex' ts) where
    maxBoundIndex' (Tm' xs (Left (Bound x)) ts)
        = max 0 (max x (maxBoundIndex ts) - length xs)
    maxBoundIndex' (Tm' xs (Left _        ) ts) 
        = max 0 (maxBoundIndex ts - length xs)
    maxBoundIndex' (Tm' xs (Right t       ) ts)
        = max 0 (maxBoundIndex (t:ts) - length xs)

bind :: Int -> [Tm'] -> Either Name Tm' -> Either Name Tm'
bind n ts (Left (Free  x)) = Left (Free x)
bind n ts (Left (Con   x)) = Left (Con  x)
bind n ts (Left (Bound x))
    | x >= n + length ts = error "bind: bound outside term"
    | x >= n             = if maxBoundIndex ts > 0 then
                             error "bind: bound outside term (in ts)"
                           else
                             Right (reverse ts !! (x - n))
    | otherwise          = Left (Bound x)
bind n ts (Right t) = Right (bindR n ts t)

bindR :: Int -> [Tm'] -> Tm' -> Tm'
bindR n ts (Tm' ys f ss) = Tm' ys (bind n ts f) (map (bindR n ts) ss)

substFree :: Idx -> Tm' -> Tm' -> Tm'
substFree x tm (Tm' bs (Left (Free x')) as) | x == x'
    = Tm' bs (Right tm) (map (substFree x tm) as)
substFree x tm (Tm' bs (Left y) as)
    = Tm' bs (Left y) (map (substFree x tm) as)
substFree x tm (Tm' bs (Right y) as)
    = Tm' bs (Right (substFree x tm y)) (map (substFree x tm) as)

applySubst :: SubstitutionPair -> Nf' -> Nf'
applySubst (x, nf2tm -> tm') (nf2tm -> tm)
    = tm2nf (normalize (substFree x tm' tm))

-- test

nfId = Nf' [base' 0] (Bound 0) []
--  tmIdId = Tm' 


test1 = applySubst (0, nfId) (Nf' [] (Free 0) [nfId])
