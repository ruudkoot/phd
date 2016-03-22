{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Main where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State

import Data.Maybe

import           Data.Set        hiding (map)
import qualified Data.Set as Set

-- | Utility | ------------------------------------------------------------[X]--

for = flip map

statefulForM :: Monad m => s -> [a] -> (s -> a -> m (s, b)) -> m (s, [b])
statefulForM s []     f = return (s, [])
statefulForM s (x:xs) f = do
    (s',  x' ) <- f s x
    (s'', xs') <- statefulForM s' xs f
    return (s'', x' : xs')

-- * Debugging * ------------------------------------------- UNUSED! ------[X]--

(x:xs) !!! 0 = x
[]     !!! _ = error "!!!"
(x:xs) !!! n = xs !!! (n-1)

-- * Sets * ---------------------------------------------------------------[X]--

-- UNUSED
unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f ss = unions (map f (toList ss))

unionMap' :: Ord b => (a -> Set b) -> [a] -> Set b
unionMap' f ss = unions (map f ss)

-- | General framework | --------------------------------------------------[ ]--

-- * Types * --------------------------------------------------------------[ ]--

data Signature sort
    = [sort] :=> sort
  deriving (Eq, Show)

data SimpleType sort
    = [SimpleType sort] :-> sort
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set

base :: sort -> SimpleType sort
base = ([] :->)

infix 4 :->

sig2ty :: Signature sort -> SimpleType sort
sig2ty (bs :=> b) = map base bs :-> b

type UnificationProblem sort sig
    = [(AlgebraicTerm sort sig, AlgebraicTerm sort sig)]

type Subst      sort sig = [      AlgebraicTerm sort sig ]
type DenseSubst sort sig = [(Int, AlgebraicTerm sort sig)]

sparsifySubst :: Env sort -> DenseSubst sort sig -> Subst sort sig
sparsifySubst env subst = for [0..] $ \i ->
    case lookup i subst of
        Nothing -> freeV env i
        Just tm -> tm

class (Ord sort, Bounded sig, Enum sig, Ord sig) => Theory sort sig | sig -> sort where
    -- FIXME: arbitrary Ord for Set (was Eq)
    constants :: [sig]
    constants =  [minBound .. maxBound]
    signature :: sig -> Signature sort
    unify     :: UnificationProblem sort sig -> Maybe (Subst sort sig)

-- NOTE: What we call 'constants', Qian & Wang call 'function symbols'. Their
-- constants are function symbols of base type.
data Atom sig
    = Bound Int     -- lambda-bound variables       (rigid)
    | FreeV Int     -- free variables               (flexible)
    | FreeC Int     -- free constants               (rigid)
    | Const sig     -- signature-bound constants    (rigid)
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
unFreeV :: Atom sig -> Int
unFreeV (FreeV x) = x

isBound :: Atom sig -> Bool
isBound (Bound _) = True
isBound _         = False

isFreeV :: Atom sig -> Bool
isFreeV (FreeV _) = True
isFreeV _         = False

isFreeC :: Atom sig -> Bool
isFreeC (FreeC _) = True
isFreeC _         = False

isConst :: Atom sig -> Bool
isConst (Const _) = True
isConst _         = False
  
-- NOTE: does not enforce function constants to be first-order
--       does not enforce the whole term to be first-order
data AlgebraicTerm sort sig
    = A [SimpleType sort] (Atom sig) [AlgebraicTerm sort sig]
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
hd :: AlgebraicTerm sort sig -> Atom sig
hd (A _ a _) = a
  
fv :: AlgebraicTerm sort sig -> [Int]
fv (A _ (FreeV f) es) = f : concatMap fv es
fv (A _ _         es) =     concatMap fv es

isRigid :: AlgebraicTerm sort sig -> Bool
isRigid (A _ (Bound _) _) = True
isRigid (A _ (FreeV _) _) = False
isRigid (A _ (FreeC _) _) = True
isRigid (A _ (Const _) _) = True

-- Convert an atom into an eta-long term.
atom2term :: Theory sort sig => Env sort -> Env sort -> Atom sig -> AlgebraicTerm sort sig
atom2term envF envB (Bound n) =
    let (xs :-> _) = envB !! n
     in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])
atom2term envF envB (FreeV n) =
    let (xs :-> _) = envF !! n
     in A xs (FreeV $ length xs + n) (map (bound xs) [0 .. length xs - 1])
atom2term envF envB (Const c) =
    let (xs :-> _) = sig2ty (signature c)
     in A xs (Const               c) (map (bound xs) [0 .. length xs - 1])

-- eta-long variables

type Env sort = [SimpleType sort]

freeV :: Env sort -> Int -> AlgebraicTerm sort sig
freeV env n
    = let (xs :-> _) = env !! n
       in A xs (FreeV n) (map (bound xs) [0 .. length xs - 1])

bound :: Env sort -> Int -> AlgebraicTerm sort sig
bound env n
    = let (xs :-> _) = env !! n
       in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])

substForFreeV :: Env sort -> AlgebraicTerm sort sig -> Int -> Subst sort sig
substForFreeV env v f = map (freeV env) [0 .. f - 1] ++ [v] ++ map (freeV env) [f + 1 ..]

type TermPair   sort sig = (AlgebraicTerm sort sig, AlgebraicTerm sort sig)
type TermSystem sort sig = [TermPair sort sig]


-- * Substitution and reduction * ----------------------------------------------

applySubstAndReduce :: Subst sort sig -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
applySubstAndReduce subst (A xs (FreeV f) ys)
    = let A xs' a ys' = subst !! f
       in reduce xs xs' a ys' ys
applySubstAndReduce subst u
    = u

bindAndReduce :: Subst sort sig -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
bindAndReduce zs (A xs (Bound b) ys)
    = let A xs' a ys' = zs !! b
       in reduce xs xs' a ys' ys
bindAndReduce zs u
    = u
    
reduce :: Env sort -> Env sort -> Atom sig -> Subst sort sig -> Subst sort sig -> AlgebraicTerm sort sig
reduce xs xs' a ys' ys
    | length xs' == length ys
        = let ys'' = map (bindAndReduce ys) ys'
           in case a of
                Bound b -> let A xsB aB ysB = ys !! b
                            in reduce xs xsB aB ysB ys''
                FreeV f -> A xs (FreeV f) ys''
                Const c -> A xs (Const c) ys''
    | otherwise = error "reduce: length xs' /= length ys"


-- * Partial bindings * ---------------------------------------------------[ ]--

typeOfAtom :: Theory sort sig => Env sort -> Atom sig -> State (Env sort, Env sort) (SimpleType sort)
typeOfAtom env (Bound b) = return $ env !! b
typeOfAtom _   (FreeV f) = do
    (env, _) <- get
    return $ env !! f
typeOfAtom _   (FreeC f) = do
    (_, env) <- get
    return $ env !! f
typeOfAtom _   (Const c) = return $ sig2ty (signature c)

typeOfFreeV :: Int -> State (Env sort, Env sort) (SimpleType sort)
typeOfFreeV f = do
    (env, _) <- get
    return $ env !! f

-- NOTE: assuming eta-long as always
typeOfTerm :: Theory sort sig => Env sort -> AlgebraicTerm sort sig -> State (Env sort, Env sort) (SimpleType sort)
typeOfTerm envB (A xs a ys) = do
    _ :-> r <- typeOfAtom (xs ++ envB) a
    return $ xs :-> r

freshAtom :: SimpleType sort -> State (Env sort, Env sort) (Atom sig)
freshAtom t = do
    (envV, envC) <- get
    put (envV ++ [t], envC)
    return $ FreeV (length envV)

partialBinding :: Theory b s => SimpleType b -> Atom s -> State (Env b, Env b) (AlgebraicTerm b s)
partialBinding (as :-> b) a = do
    cs :-> b' <- typeOfAtom as a
    if b /= b' then
        error "partialBinding: b /= b'"
    else do

        let generalFlexibleTerm (fs :-> c') = do
                h <- freshAtom (as ++ fs :-> c')
                return $ A fs h $ map (bound $ fs ++ as) $
                    [length fs .. length fs + length as - 1] ++ [0 .. length fs - 1]

        gfts <- mapM generalFlexibleTerm cs
        return (A as a gfts)

-- * Maximal flexible subterms (Qian & Wang) * ----------------------------[ ]--

pmfs :: Theory sort sig => AlgebraicTerm sort sig
                            -> Set ([SimpleType sort], AlgebraicTerm sort sig)
pmfs = pmfs' []

pmfs' :: Theory sort sig => [SimpleType sort] -> AlgebraicTerm sort sig
                            -> Set ([SimpleType sort], AlgebraicTerm sort sig)
pmfs' ys (A xs (FreeV f) ss) = singleton (xs ++ ys, A [] (FreeV f) ss)
pmfs' ys (A xs a         ss) = unionMap' (pmfs' (xs ++ ys)) ss

-- * Transformation rules (Qian & Wang) * ---------------------------------[ ]--

-- TODO: check invariant: length envV == length theta'

type TransformationRule b s = TermPair b s -> TermSystem b s -> State (Env b, Env b) (Maybe (TermSystem b s))

type     Conf b s = (Subst b s,                 TermSystem b s)
type HeadConf b s = (Subst b s, TermPair   b s, TermSystem b s)
type PartConf b s = (Subst b s, TermSystem b s, TermSystem b s)

transformAbs :: Theory b s => HeadConf b s -> State (Env b, Env b) (Maybe (Conf b s))
transformAbs (theta', (u,v), ss) | isRigid u || isRigid v = do
    -- maximal flexible subterms
    let ps = toList $ pmfs u `union` pmfs v
    -- conditional mapping
    -- NOTE: Unlike the paper we don't bother applying xs to H yet, as this
    --       will not necessarily form an eta-long term. Take care of this in
    --       the application function instead (xs are remembered in the
    --       conditional mapping anyway).
    hs <- forM ps $ \(xs,w) -> do
            xs' :-> r <- typeOfTerm [] w
            freshAtom (xs ++ xs' :-> r)
    let phi = zipWith (\(xs,w) h -> (xs,w,h)) ps hs
    (envV, _) <- get
    return $ Just $
        ( if length theta' /= unFreeV (head hs) then
            error "transformAbs: assertion failed - substitution too short (or long)"
          else
            theta' ++ map (\(xs,A xs' a' ys',_h) -> A (xs'++xs) a' ys') phi
        , [(applyConditionalMapping phi u,applyConditionalMapping phi v)]
          ++ map (\(xs,A xs' a' ys',h) -> (atom2term envV [] h, A (xs'++xs) a' ys')) phi
          ++ ss
        )
transformAbs _ | otherwise = error "transformAbs: assumptions violated"
                          -- return Nothing

type ConditionalMapping b s = [([SimpleType b], AlgebraicTerm b s, Atom s)]

applyConditionalMapping :: Theory b s => ConditionalMapping b s
                                    -> AlgebraicTerm b s -> AlgebraicTerm b s
applyConditionalMapping = undefined

-- ss' assumed to be E-acceptable
-- may be non-deterministic if the unification algorithm isn't unary
--              (AG and BR unification are of unification type 1, though!)
transformEUni :: Theory b s => PartConf b s -> State (Env b, Env b) (Maybe (Conf b s))
transformEUni (theta, ss', ss) = do
    let ps = toList $ Set.map snd (unionMap' (\(u,v) -> pmfs u `union` pmfs v) ss')
    rho <- forM ps $ \w -> do
                 t <- typeOfTerm [] w
                 y <- freshAtom t
                 return (w,y)
    let xss    = map (\(A [] _ xs,_) -> xs) rho
    let ys     = map snd rho
    let rhoSS' = map (applyOrderReduction rho *** applyOrderReduction rho) ss'
                    -- FIXME: ^ remove duplicates (is a set)
    let Just sigma = unify rhoSS'
                    -- FIXME: unification can fail (propagate failure)
    (_, phis) <- statefulForM [] (zip xss ys) $ \s (xs_i, FreeV y) -> do
                    let qs = toList $ pmfs (sigma !! y)
                    statefulForM s qs $ \s' (us, z) -> do
                        case lookup (z, xs_i, us) s' of
                            Nothing -> do
                                tyxs_i <- mapM (typeOfTerm []) xs_i
                                _ :-> t <- typeOfTerm [] z
                                z' <- freshAtom (tyxs_i ++ us :-> t)
                                return ( ((z, xs_i, us), z') : s'
                                       , (us, z, z')              )
                            Just z' -> do
                                return ( s', (us, z, z') )
    -- FIXME: SHADOWS THE OTHER 'theta'!
    theta <- forM (zip3 phis ys ps) $ \(phi, FreeV y, A [] (FreeV g) xs) -> do
                ts <- mapM (typeOfTerm []) xs
                let (A us a as) = applyConditionalMapping phi (sigma !! y)
                return (g, A (us ++ ts) a as)
    (envV, _) <- get
    let theta'  = map (\(x,y) -> (freeV envV x, y)) theta
    let theta'' = sparsifySubst envV theta
    return $ Just $
        ( error "TODO"
        , theta' ++ map (applySubstAndReduce theta'' *** applySubstAndReduce theta'') ss
        )

type OrderReduction b s = [(AlgebraicTerm b s, Atom s)]

applyOrderReduction :: Theory b s => OrderReduction b s
                                    -> AlgebraicTerm b s -> AlgebraicTerm b s
applyOrderReduction = undefined

-- (u,v) assumed to be flexible-rigid (i.e., not rigid-flexible)
-- are we only non-deterministic locally (choice of 'b') or also globally
--                  (choice of '(u,v)')?
transformBin :: Theory b s => HeadConf b s -> State (Env b, Env b) [Conf b s]
transformBin (theta', (u@(A xs (FreeV f) us), v@(A _xs a vs)), ss)
  | xs == _xs && isRigid v
    = do (envV, envC) <- get
         ts :-> t <- typeOfFreeV f
         let bs = concat  -- FIXME: can 'b' also be a free variable?
                    [ if isFreeC a && any
                            (\u -> isBound (hd u) || (isFreeC (hd u) && hd u /= a)) us
                      then
                        []
                      else
                        map Bound [0 .. length ts - 1]           
                    , map Const constants  -- FIXME: can prune this if E is collapse-free
                    , if isFreeC a then
                        [a]
                      else
                        map FreeC [0 .. length envC - 1]
                    ]
         pbs <- mapM (partialBinding (ts :-> t)) bs
         (envV, envC) <- get
         return $ for pbs $ \pb ->
            let theta = sparsifySubst envV [(f, pb)]
            in ( let (A ys b zs) = theta' !! f
                     theta''     = for zs $ \(A ys' b' zs') -> A (ys' ++ ys) b' zs'
                  in theta' ++ theta''
               , (freeV envV f, pb)
                    : map (applySubstAndReduce theta *** applySubstAndReduce theta) ss
               )
transformBin _ = error "transformBin: assumptions violated"

-- * Control strategy (Qian & Wang) * -------------------------------------[ ]--

controlStrategy = undefined

-- | Examples | -----------------------------------------------------------[ ]--

-- * Maximal flexible subterms * ------------------------------------------[ ]--

data Sig' = F | G | H
  deriving (Eq, Bounded, Enum, Ord, Show)
  
instance Theory Sort Sig' where
    signature H = [Real, Real] :=> Real
    unify       = undefined

u0 = let f  = 0
         g  = 1
         x  = 0
         y  = 1
         x' = 1
         y' = 2
         z  = 0
      in A [base Real, base Real] (Const H)
            [A [] (FreeV f) [A [] (Bound x) []]
            ,A [base Real] (FreeV f) [A [] (Bound x') []]
            ,A [] (FreeV f) [A [] (FreeV g) [A [] (Bound x) []]]
            ]

-- | Higher-order dimension types | ---------------------------------------[ ]--

data Sort
    = Real
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
data Sig
    = Mul
    | Inv
    | Unit
  deriving (Eq, Bounded, Enum, Ord, Show)  -- FIXME: arbitrary Ord for Set

instance Theory Sort Sig where
    signature Mul  = [Real, Real] :=> Real
    signature Inv  = [Real]       :=> Real
    signature Unit = []           :=> Real
    
    unify          = unify'
    
-- * Unification modulo Abelian groups * ----------------------------------[ ]--

unify' :: UnificationProblem Sort Sig -> Maybe (Subst Sort Sig)
unify' = undefined
