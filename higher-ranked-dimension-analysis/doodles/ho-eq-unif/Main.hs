{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ViewPatterns           #-}

module Main where

import Control.Applicative ((<$>))
import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List

import Data.Function
import Data.List (minimumBy, partition, sort, sortBy)
import Data.Maybe

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set        hiding (filter, foldr, map, partition, null)
import qualified Data.Set as Set

-- | Utility | ------------------------------------------------------------[ ]--

for = flip map

statefulForM :: Monad m => s -> [a] -> (s -> a -> m (s, b)) -> m (s, [b])
statefulForM s []     f = return (s, [])
statefulForM s (x:xs) f = do
    (s',  x' ) <- f s x
    (s'', xs') <- statefulForM s' xs f
    return (s'', x' : xs')

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

maximum' :: Ord a => a -> [a] -> a
maximum' x xs = maximum (x : xs)

-- order in which the list elements are fed to 'f' is weird,
-- (but that does not matter if they represent sets)
forEachWithContext :: (a -> [a] -> Maybe b) -> [a] -> [b]
forEachWithContext f = forEachWithContext' []
  where
    forEachWithContext' ys []     = []
    forEachWithContext' ys (x:xs) = case f x (ys ++ xs) of
                            Nothing ->     forEachWithContext' (x : ys) xs
                            Just z  -> z : forEachWithContext' (x : ys) xs

-- * Debugging * ------------------------------------------- UNUSED! ------[X]--

xxs !!! m = xxs !!!~ m
 where
    (x:xs) !!!~ 0 = x
    []     !!!~ _ = error $ show xxs ++ " !!! " ++ show m
    (x:xs) !!!~ n = xs !!!~ (n-1)

-- * Sets * ---------------------------------------------------------------[X]--

-- UNUSED
unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f ss = unions (map f (toList ss))

unionMap' :: Ord b => (a -> Set b) -> [a] -> Set b
unionMap' f ss = unions (map f ss)

-- | General framework | --------------------------------------------------[ ]--

-- * Types * --------------------------------------------------------------[X]--

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

class (Ord sort, Bounded sig, Enum sig, Ord sig, Show sort, Show sig) => Theory sort sig | sig -> sort where
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

isConst :: Atom sig -> Bool -- UNUSED
isConst (Const _) = True
isConst _         = False

-- NOTE: does not enforce function constants to be first-order
--       does not enforce the whole term to be first-order
data AlgebraicTerm sort sig
    = A [SimpleType sort] (Atom sig) [AlgebraicTerm sort sig]
  deriving (Eq, Ord, Show)  -- FIXME: arbitrary Ord for Set
  
hd :: AlgebraicTerm sort sig -> Atom sig
hd (A _ a _) = a
  
isRigid :: AlgebraicTerm sort sig -> Bool
isRigid = not . isFreeV . hd

-- eta-long variables
type Env sort = [SimpleType sort]

bound :: Env sort -> Int -> AlgebraicTerm sort sig
bound envB n
    = let (xs :-> _) = envB !! n
       in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])

freeV :: Env sort -> Int -> AlgebraicTerm sort sig
freeV envV n
    = let (xs :-> _) = envV !! n
       in A xs (FreeV n) (map (bound xs) [0 .. length xs - 1])

-- Convert an atom into an eta-long term.
atom2term :: Theory sort sig =>
        Env sort -> Env sort -> Env sort -> Atom sig -> AlgebraicTerm sort sig
atom2term envB _envV _envC (Bound n) =
    let (xs :-> _) = envB !! n
     in A xs (Bound $ length xs + n) (map (bound xs) [0 .. length xs - 1])
atom2term _envB envV _envC (FreeV n) =
    let (xs :-> _) = envV !! n
     in A xs (FreeV n) (map (bound xs) [0 .. length xs - 1])
atom2term _envB _envV envC (FreeC n) =
    let (xs :-> _) = envC !! n
     in A xs (FreeC n) (map (bound xs) [0 .. length xs - 1])
atom2term _envB _envV _envC (Const c) =
    let (xs :-> _) = sig2ty (signature c)
     in A xs (Const c) (map (bound xs) [0 .. length xs - 1])

type TermPair   sort sig = (AlgebraicTerm sort sig, AlgebraicTerm sort sig)
type TermSystem sort sig = [TermPair sort sig]

-- * Substitution and reduction * -----------------------------------------[.]--

-- Raise the De Bruijn index of unbound variables in a term by 'k'.
raise :: Int -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
raise k = raise' 0
  where
    raise' n (A xs a ys)
      = let ys' = map (raise' (n + length xs)) ys
         in case a of
              Bound b ->
                if b < n + length xs then
                    A xs (Bound b) ys'
                else if b + k < n + length xs then
                    error "raise: unexpected capture"
                else
                    A xs (Bound (b + k)) ys'
              _ -> A xs a ys'
              
lower :: Int -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
lower k | k >= 0    = raise (-k)
        | otherwise = error "lower: negative"

-- Reduces \xs(\xs'.a(ys'))(ys) to \xs.a[ys/xs'](ys'[ys/xs']).
reduce :: Env sort -> Env sort -> Atom sig -> Subst sort sig -> Subst sort sig
                                                        -> AlgebraicTerm sort sig
reduce xs xs' a ys' ys
    | length xs' == length ys
        = let k    = length xs'
              ys'' = map (lower k . bindAndReduce [] xs' (map (raise k) ys)) ys'
           in case a of
                Bound b -> if b < k then
                                let A xsB aB ysB = ys !! b
                                 in reduce xs xsB aB ysB ys''
                           else A xs (Bound (b - k)) ys''
                a       -> A xs a ys''
    | length xs' > length ys
        -- this case should not occur if terms are always eta-long
        = error "reduce: length xs' > length ys"
    | length xs' < length ys
        = error "reduce: length xs' < length ys"

  where

    bindAndReduce :: Env sort -> Env sort -> Subst sort sig -> AlgebraicTerm sort sig
                                                                -> AlgebraicTerm sort sig
    bindAndReduce ns xs' ys (A zs a zs')
      | length xs' == length ys
        = let k    = length (zs ++ ns)
              zs'' = map (bindAndReduce (zs ++ ns) xs' ys) zs'
           in case a of                             -- ^ why not raise here (instead)?
                Bound b ->                          -- FIXME: double raising does not
                    if b < k then                   --        trigger any testcase!
                        A zs (Bound b) zs''
                    else if b < k + length ys then
                        let (A us a' vs) = raise k (ys !! (b - k))
                         in reduce zs us a' vs zs'' 
                    else
                        A zs (Bound b) zs''
                _ -> A zs a zs''
      | otherwise = error
            "bindAndReduce: length xs' /= length ys"

substFreeVAndReduce :: Subst sort sig -> AlgebraicTerm sort sig -> AlgebraicTerm sort sig
substFreeVAndReduce subst (A xs (FreeV f) ys)
    = let ys'       = map (substFreeVAndReduce subst) ys
          A us a vs = subst !! f
       in reduce xs us a vs ys'
substFreeVAndReduce subst u
    = u
   
-- * Partial bindings * ---------------------------------------------------[X]--

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

-- introduces new fresh variables, like completion...
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

-- * Maximal flexible subterms (Qian & Wang) * ----------------------------[X]--

-- NOTE: the binders are not returned in the same order as in the paper!
--       they are also not applied in the same order by conditional mappings
--       (this should not matter, as long as it is done consistently)


type ConditionalMapping b s = Map ([SimpleType b], AlgebraicTerm b s) (Atom s)
type OrderReduction     b s = Map (AlgebraicTerm b s) (Atom s)


pmfs :: Theory sort sig => AlgebraicTerm sort sig
                            -> Set ([SimpleType sort], AlgebraicTerm sort sig)
pmfs = pmfs' []
  where
    pmfs' :: Theory sort sig => [SimpleType sort] -> AlgebraicTerm sort sig
                                -> Set ([SimpleType sort], AlgebraicTerm sort sig)
    pmfs' ys (A xs (FreeV f) ss) = singleton (xs ++ ys, A [] (FreeV f) ss)
    pmfs' ys (A xs a         ss) = unionMap' (pmfs' (xs ++ ys)) ss


applyConditionalMapping
    :: Theory b s => ConditionalMapping b s -> AlgebraicTerm b s -> AlgebraicTerm b s
applyConditionalMapping condMap = applyConditionalMapping' []
  where
    applyConditionalMapping' ctx (A xs (FreeV f) ss)
        = case Map.lookup (xs ++ ctx, A [] (FreeV f) ss) condMap of
            Nothing -> A xs (FreeV f) (map (applyConditionalMapping' (xs ++ ctx)) ss)
            Just a  -> A xs a (map (bound (xs ++ ctx)) [0 .. length (xs ++ ctx) - 1])
    applyConditionalMapping' ctx (A xs a ss)
        = A xs a (map (applyConditionalMapping' (xs ++ ctx)) ss)


-- FIXME: this can make a term non eta-long
--        (do this while making a term first-order instead?)
applyOrderReduction
    :: Theory b s => OrderReduction b s -> AlgebraicTerm b s -> AlgebraicTerm b s
applyOrderReduction ordRedMap (A xs a ss)
    = case Map.lookup (A [] a ss) ordRedMap of
        Nothing -> A xs a (map (applyOrderReduction ordRedMap) ss)
        Just a' -> A xs a' []

isTrivialFlexibleSubterm :: Theory b s => Env b -> AlgebraicTerm b s -> Bool
isTrivialFlexibleSubterm ctx (A [] (FreeV _) ys)
    = ys == map (\n -> bound ctx n) [0 .. length ctx - 1]
isTrivialFlexibleSubterm _ _
    = False
        
isEAcceptable :: Theory b s => TermSystem b s -> Bool
isEAcceptable ss
    = let ps = toList $ unionMap' (\(u,v) -> pmfs u `union` pmfs v) ss
       in all (uncurry isTrivialFlexibleSubterm) ps


-- * Transformation rules (Qian & Wang) * ---------------------------------[ ]--

-- FIXME: does theta' apply only to FreeV's or also to FreeC's?
-- FIXME: do we need the Maybe in the return type (or handle this in controlStrategy?)
-- TODO: check invariant: length envV == length theta'

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
    let phi  = zipWith (\(xs,w) h -> ((xs,w),h)) ps hs
    let phi' = Map.fromList phi
    (envV, envC) <- get
    return $ Just $
        ( if length theta' /= unFreeV (head hs) then
            error "transformAbs: assertion failed - substitution too short (or long)"
          else
            theta' ++ for phi (\((xs,A xs' a' ys'),_h) ->
                                    substFreeVAndReduce theta' (A (xs'++xs) a' ys'))
        , [(applyConditionalMapping phi' u,applyConditionalMapping phi' v)]
          ++ map (\((xs,A xs' a' ys'),h) -> (atom2term [] envV envC h, A (xs'++xs) a' ys')) phi
          ++ ss
        )
transformAbs _ | otherwise = error "transformAbs: assumptions violated"


-- FIXME: we "lose" the top-level binder in an inconvenient way. e.g.,
--        * the mock [base Real]s we have to pass to typeOfTerm
--        * when reconstruction the binder and arguments of the higher order term
-- FIXME: substitutions should be partial?
-- FIXME: don't pollute the environment with temporary variables (Y_i, Z_i)
-- NOTE: may be non-deterministic if the unification algorithm isn't unary
--       (while AG and BR unification with nullary constants are of unitary,
--       AG and BR unification with function symbols is finitary!)
-- transformEUni :: Theory b s => PartConf b s -> State (Env b, Env b) (Maybe (Conf b s))
transformEUni :: PartConf Sort Sig -> State (Env Sort, Env Sort) (Maybe (Conf Sort Sig))
transformEUni (theta', ss', ss) | isEAcceptable ss' = do
    let ps = toList $ Set.map snd (unionMap' (\(u,v) -> pmfs u `union` pmfs v) ss')

    rho <- forM ps $ \w -> do
                 t <- typeOfTerm [] w
                 y <- freshAtom t
                 return (w,y)
    let rho'   = Map.fromList rho
    -- FIXME: applyOrderReduction seems superfluous, just drop the arguments
    --        from G, to obtain Y (or do it in a more straightforward fashion)?
    let rhoSS' = map (applyOrderReduction rho' *** applyOrderReduction rho') ss'
                    -- FIXME: ^ remove duplicates (is a set)

    -- FIXME: reinterpret rhoSS' as a first-order system here!
    --        (fold in applyOrderReduction?)

    let Just sigma = unify rhoSS'
                    -- FIXME: unification can fail (propagate failure)
                    
    {- MOCK!!! -}
    FreeV 4 <- freshAtom (base Real)    -- FIXME: or FreeC?
    FreeV 5 <- freshAtom (base Real)
    let sigma = [error "F0"             -- FIXME: rather not see those in here...
                ,error "F1"             --        (env ++ sigma) !! y
                ,A  [base Real]         -- FIXME: [base Real] shouldn't be here, yet
                    (Const Mul)         --        make everything so much easier...
                    [A [] (FreeV 4) []  --        ("reconstructing the missing binder")
                    ,A [] (Const Mul) [A [] (Bound 0) [], A [] (FreeV 5) []]]
                ,A [base Real] (FreeV 4) []
                ]
    {- MOCK!!! -}

    let xss    = map (\(A [] _ xs,_) -> xs) rho
    let ys     = map snd rho
    -- FIXME: commented out code is related to "reconstructing the missing binder"
    (_, phis) <- statefulForM [] (zip xss ys) $ \s (xs_i, FreeV y) -> do
                    let qs = toList $ pmfs (sigma !! y)
                    statefulForM s qs $ \s' (us, z) -> do
                        case lookup (z, xs_i, us) s' of
                            Nothing -> do
                                tyxs_i <- mapM (typeOfTerm [{-!-}base Real{-!-}]) xs_i
                                _ :-> t <- typeOfTerm [{-!-}base Real{-!-}] z
                                -- z' <- freshAtom (tyxs_i ++ us :-> t)
                                z' <- freshAtom ({- tyxs_i ++ -} us :-> t)  -- FIXME
                                return ( ((z, xs_i, us), z') : s'
                                       , ((us, z), z')              )
                            Just z' -> do
                                return ( s', ((us, z), z') )

    -- FIXME: commented out code is related to "reconstructing the missing binder"
    theta <- forM (zip3 phis ys ps) $ \(phi, FreeV y, A [] (FreeV g) xs) -> do
                -- ts <- mapM (typeOfTerm [{-!-}base Real{-!-}]) xs
                let (A us a as) = applyConditionalMapping (Map.fromList phi) (sigma !! y)
                -- return (g, A (us ++ ts) a as)
                return (g, A us a as)
    (envV, _) <- get
    let thetaD = map (\(x,y) -> (freeV envV x, y)) theta
    let thetaS = sparsifySubst envV theta

    return $ Just $
        ( error "TODO"
        , thetaD ++ map (substFreeVAndReduce thetaS *** substFreeVAndReduce thetaS) ss
        )

transformEUni _ | otherwise = error "transformEUni: assumptions violated"

-- (u,v) assumed to be flexible-rigid (i.e., not rigid-flexible)
-- are we only non-deterministic locally (choice of 'b') or also globally
--                  (choice of '(u,v)')?
-- FIXME: don't cross-pollute the environments of different branches
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
                    : map (substFreeVAndReduce theta *** substFreeVAndReduce theta) ss
               )
transformBin _ = error "transformBin: assumptions violated"

-- * Control strategy (Qian & Wang) * -------------------------------------[ ]--

controlStrategy = error "controlStrategy"

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
    
-- | Unification modulo Abelian groups | ----------------------------------[ ]--

unify' :: UnificationProblem Sort Sig -> Maybe (Subst Sort Sig)
unify' = error "unify'"



-- * AG-unification with free nullary constants (unitary) * ---------------[X]--

-- Kennedy (1996) / Lankford, Butler & Brady (1984) + Knuth (1969)

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

-- Solve a single equation in AG, while treating a set of given variables as
-- constants.
agUnif1TreatingAsConstant
    :: TermAlg Sig f' Int Int
    => [T Sig f' Int Int]               -- set of marked variables SMV
    -> T Sig f' Int Int                 -- expression s
    -> T Sig f' Int Int                 -- expression t
    -> Maybe (AGUnifProb Sig f' Int Int)
agUnif1TreatingAsConstant smv s t
    = let numV1  = max (numX  s) (numX  t)
          numV2  = max (numX' s) (numX' t)
          numC'  = max (numC  s) (numC  t)
          s'     = constantify numC' smv s
          t'     = constantify numC' smv t
          numC'' = max (numC s') (numC t')
       in case agUnif1 (toExp' numV1 numV2 numC'' (s', t')) of
            Nothing -> Nothing
            Just agSubst -> Just $ map (deconstantify numC' *** deconstantify numC')
                                       (fromExp numV1 agSubst)
       
constantify
    :: TermAlg Sig f' Int Int
    => Int
    -> [T Sig f' Int Int]
    -> T Sig f' Int Int
    -> T Sig f' Int Int
constantify numC' smv = constantify'
  where
    constantify' (X  x    ) | X  x  `elem` smv = C (numC' + 2 * x)
                            | otherwise        = X x
    constantify' (X' x'   ) | X' x' `elem` smv = C (numC' + 2 * x' + 1)
                            | otherwise        = X' x'
    constantify' (C  c    ) = C  c
    constantify' (F  f  ts) = F  f  (map constantify' ts)
    constantify' (F' f' ts) = F' f' (map constantify' ts)
    
deconstantify
    :: TermAlg Sig f' Int Int
    => Int
    -> T Sig f' Int Int
    -> T Sig f' Int Int
deconstantify numC' = deconstantify'
  where
    deconstantify' (X  x ) = X  x
    deconstantify' (X' x') = X' x'
    deconstantify' (C  c ) | c < numC'                        = C  c
                           | (x ,0) <- (c - numC') `divMod` 2 = X  x
                           | (x',1) <- (c - numC') `divMod` 2 = X' x'
    deconstantify' (F  f  ts) = F  f  (map deconstantify' ts)
    deconstantify' (F' f' ts) = F' f' (map deconstantify' ts)

-- * AG-unification with free function symbols * --------------------------[ ]--

-- Boudet, Jouannaud & Schmidt-Schauß (1989)

-- FIXME: instead of X and X': x --> Either x Int?
-- FIXME: combine C and F?
data T f f' c x
    = X  x                  -- variables            (E and E')
    | X' Int                -- fresh variables      (E and E')
    | C  c                  -- nullary constants    (E)
    | F  f  [T f f' c x]    -- function symbols     (E)
    | F' f' [T f f' c x]    -- function symbols     (E')
  deriving (Eq, Ord, Show)

type AGUnifProb f f' c x = [(T f f' c x, T f f' c x)]
  
class    (Ord f, Ord f', Ord c, Ord x) => TermAlg f f' c x
instance (Ord f, Ord f', Ord c, Ord x) => TermAlg f f' c x

newT :: T f f' c x -> State (Int, AGUnifProb f f' c x) Int
newT t = do (n, xs') <- get
            modify (\(n, xs') -> (n+1, xs' ++ [(X' n,t)]))     -- performance...
            return n
            
newV :: State Int (T f f' c x)
newV = do n <- get
          modify (+1)
          return (X' n)

isVar :: T f f' x c -> Bool
isVar (X  _) = True
isVar (X' _) = True
isVar _      = False

vars :: T f f' c x -> [x]
vars (X  x   ) = [x]
vars (X' _   ) = []
vars (C  _   ) = []
vars (F  _ ts) = concatMap vars ts
vars (F' _ ts) = concatMap vars ts

vars' :: T f f' c x -> [Int]
vars' (X  _   ) = []
vars' (X' x   ) = [x]
vars' (C  _   ) = []
vars' (F  _ ts) = concatMap vars' ts
vars' (F' _ ts) = concatMap vars' ts

allVars :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
allVars = unionMap' (\(s,t) -> allVars' s `union` allVars' t)
  where
    allVars' t@(X  _   ) = singleton t
    allVars' t@(X' _   ) = singleton t
    allVars'   (C  _   ) = empty
    allVars'   (F  _ ts) = unionMap' allVars' ts
    allVars'   (F' _ ts) = unionMap' allVars' ts

homogeneous :: T f f' c x -> State (Int, AGUnifProb f f' c x) (T f f' c x)
homogeneous (X  x    ) = return (X  x )
homogeneous (X' x'   ) = return (X' x')
homogeneous (C  c    ) = return (C  c )
homogeneous (F  f  ts) = F f <$> mapM homogeneous ts
homogeneous (F' f' ts) = X'  <$> newT (F' f' ts)

homogeneous' :: T f f' c x -> State (Int, AGUnifProb f f' c x) (T f f' c x)
homogeneous' (X  x    ) = return (X  x )
homogeneous' (X' x'   ) = return (X' x')
homogeneous' (C  c    ) = X'    <$> newT (C c)
homogeneous' (F  f  ts) = X'    <$> newT (F f ts)
homogeneous' (F' f' ts) = F' f' <$> mapM homogeneous' ts

homogeneous'' :: T f f' c x -> State Int (T f f' c x, AGUnifProb f f' c x)
homogeneous'' (X  x   ) = return (X  x , [])
homogeneous'' (X' x'  ) = return (X' x', [])
homogeneous'' (C  c   ) = return (C  c , [])
homogeneous'' t@(F _ _) = do
    n <- get
    let (t',(n',xs)) = runState (homogeneous t) (n, [])
    put n'
    return (t', xs)
homogeneous'' t@(F' _ _) = do
    n <- get
    let (t',(n',xs)) = runState (homogeneous' t) (n, [])
    put n'
    return (t', xs)

isPureE :: T f f' c x -> Bool
isPureE (X  _   ) = True
isPureE (X' _   ) = True
isPureE (C  _   ) = True
isPureE (F  _ ts) = all isPureE ts
isPureE (F' _ _ ) = False

isPureE' :: T f f' c x -> Bool
isPureE' (X  _   ) = True
isPureE' (X' _   ) = True
isPureE' (C  _   ) = False
isPureE' (F  _ _ ) = False
isPureE' (F' _ ts) = all isPureE' ts

isHeterogeneous :: T f f' c x -> Bool
isHeterogeneous t = let ((_,rs),_) = runState (homogeneous'' t) 0 in not (null rs)

subst :: TermAlg f f' c x => x -> T f f' c x -> T f f' c x -> T f f' c x
subst x t t'@(X  x') | x == x'   = t
                     | otherwise = t'
subst x _ t'@(X' _ ) = t'
subst x _ t'@(C  _ ) = t'
subst x t (F  f  ts) = F  f  (map (subst x t) ts)
subst x t (F' f' ts) = F' f' (map (subst x t) ts)

subst' :: Int -> T f f' c x -> T f f' c x -> T f f' c x
subst' _ _ t'@(X  _ ) = t'
subst' x t t'@(X' x') | x == x'   = t
                      | otherwise = t'
subst' _ _ t'@(C  _ ) = t'
subst' x t (F  f  ts) = F  f  (map (subst' x t) ts)
subst' x t (F' f' ts) = F' f' (map (subst' x t) ts)

-- the unification problem sigma is assumed to be in solved form
applySubst :: TermAlg f f' x c => AGUnifProb f f' c x -> T f f' c x -> T f f' c x
applySubst sigma (X x)
    | Just t <- lookup (X  x ) sigma = t
    | otherwise                      = X x
applySubst sigma (X' x')
    | Just t <- lookup (X' x') sigma = t
    | otherwise                      = X' x'
applySubst sigma (C c     ) = C c
applySubst sigma (F  f  ts) = F  f  (map (applySubst sigma) ts)
applySubst sigma (F' f' ts) = F' f' (map (applySubst sigma) ts)

freeUnif :: TermAlg f f' c Int => AGUnifProb f f' c Int -> Maybe (AGUnifProb f f' c Int)
freeUnif = freeUnif' []
  where

    freeUnif' sol [] = Just (sortBy (compare `on` fst) sol)
    
    freeUnif' sol ((F' f1 ts1, F' f2 ts2):prob)
        -- Decompose
        | f1 == f2  = freeUnif' sol (zip ts1 ts2 ++ prob)
        -- Clash
        | otherwise = Nothing

    -- Orient
    freeUnif' sol ((   X x1   ,   X' x2 ):prob) = freeUnif' sol ((X' x2, X x1):prob)
    freeUnif' sol ((t@(F' _ _),x@(X  _ )):prob) = freeUnif' sol ((x,t):prob)
    freeUnif' sol ((t@(F' _ _),x@(X' _ )):prob) = freeUnif' sol ((x,t):prob)    

    freeUnif' sol (p@(X' x1, X x2):prob)
        -- Elimintate
        = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst' x1 (X' x2) *** subst' x1 (X' x2))

    freeUnif' sol (p@(X x1, X x2):prob)
        -- Delete
        | x1 == x2  = freeUnif' sol prob
        -- Eliminate
        | otherwise = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst x1 (X x2) *** subst x1 (X x2))
    
    freeUnif' sol (p@(X' x1, X' x2):prob)
        -- Delete
        | x1 == x2  = freeUnif' sol prob
        -- Eliminate
        | otherwise = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst' x1 (X' x2) *** subst' x1 (X' x2))

    freeUnif' sol (p@(X x, t@(F' f ts)):prob)
        -- Occurs-Check
        | x `elem` vars t = Nothing
        -- Eliminate
        | otherwise       = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst x t *** subst x t)

    freeUnif' sol (p@(X' x, t@(F' f ts)):prob)
        -- Occurs-Check
        | x `elem` vars' t = Nothing
        -- Eliminate
        | otherwise        = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst' x t *** subst' x t)

{-  -- Clash / Decompose
    freeUnif' sol ((F f1 ts1, F f2 ts2):prob)
        | f1 == f2  = freeUnif' sol (zip ts1 ts2 ++ prob)
        | otherwise = Nothing
    freeUnif' _ ((F  _ _, F' _ _):_) = Nothing
    freeUnif' _ ((F' _ _, F  _ _):_) = Nothing
    -- Orient
    freeUnif' sol ((t@(F  _ _),x@(X  _)):prob) = freeUnif' sol ((x,t):prob)
    freeUnif' sol ((t@(F  _ _),x@(X' _)):prob) = freeUnif' sol ((x,t):prob)
    -- Eliminate / Occurs-Check
    freeUnif' sol (p@(X x, t@(F f ts)):prob)
        | x `elem` vars t = Nothing
        | otherwise       = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst x t *** subst x t)
    freeUnif' sol (p@(X' x, t@(F f ts)):prob)
        | x `elem` vars' t = Nothing
        | otherwise        = freeUnif' (p:elim sol) (elim prob)
            where elim = map (subst' x t *** subst' x t)                      -}

type AGClassifiedUnifProb f f' c x = (AGUnifProb f f' c x
                                     ,AGUnifProb f f' c x
                                     ,AGUnifProb f f' c x
                                     ,AGUnifProb f f' c x)


-- FIXME: orient equations with variable on the rhs?
classify :: AGUnifProb f f' c x -> AGClassifiedUnifProb f f' c x
classify [] = ([],[],[],[])
classify (p@(s,t):ps)
    = let (pe,pe',pi,ph) = classify ps
       in case p of
            -- order matters: {x=y} in P_E'
            (s,t) | isPureE' s && isPureE' t
                -> (pe, (s,t):pe', pi, ph)
            (s,t) | isPureE s && isPureE t
                -> ((s,t):pe, pe', pi, ph)
            (s,t) | isPureE s && isPureE' t
                ->  (pe, pe', (s,t):pi, ph)
            (s,t) | isPureE' s && isPureE t                 -- orient
                ->  (pe, pe', (t,s):pi, ph)
            (s,t) | isHeterogeneous s || isHeterogeneous t  -- performance...
                -> (pe,pe',pi,(s,t):ph)
            _ -> error "classify: should not happen"


-- FIXME: does not check for idempotency (costly, might not be necessary)
inSolvedForm :: TermAlg f f' c x => AGUnifProb f f' c x -> Bool
inSolvedForm xs = all inSolvedForm' xs
                    && length xs == Set.size (Set.fromList (map fst xs))
  where inSolvedForm' (X  _, _) = True
        inSolvedForm' (X' _, _) = True
        inSolvedForm' _         = False


numX :: T f f' c Int -> Int
numX (X  x   ) = x + 1
numX (X' _   ) = 0
numX (C  _   ) = 0
numX (F  _ ts) = maximum' 0 (map numX ts)
numX (F' _ ts) = maximum' 0 (map numX ts)

numX' :: T f f' c x -> Int
numX' (X  _   ) = 0
numX' (X' x'  ) = x' + 1
numX' (C  _   ) = 0
numX' (F  _ ts) = maximum' 0 (map numX' ts)
numX' (F' _ ts) = maximum' 0 (map numX' ts)

numC :: T f f' Int x -> Int
numC (X  _   ) = 0
numC (X' _   ) = 0
numC (C  c   ) = c + 1
numC (F  _ ts) = maximum' 0 (map numC ts)
numC (F' _ ts) = maximum' 0 (map numC ts)

toExp :: Int -> Int -> Int -> T Sig f' Int Int -> AGExp1
toExp v1 v2 c s = toExp' v1 v2 c (s, F Unit [])

toExp' :: Int -> Int -> Int -> (T Sig f' Int Int, T Sig f' Int Int) -> AGExp1
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
    

fromExp :: Int -> AGSubst1 -> AGUnifProb Sig f' Int Int
fromExp v1 ss@(length -> v)
    = zipWith (\x t -> (x, fromExp' t)) (map X [0 .. v1 - 1] ++ map X' [0 .. v - v1]) ss
  where
    fromExp' :: AGExp1 -> T Sig f' Int Int
    fromExp' (splitAt v1 -> (vs,vs'),cs)
        = let xs =    map (fromExp'' X ) (filter ((/=0) . snd) (zip [0 .. v1]     vs ))
                   ++ map (fromExp'' X') (filter ((/=0) . snd) (zip [0 .. v - v1] vs'))
                   ++ map (fromExp'' C ) (filter ((/=0) . snd) (zip [0 .. ]       cs ))
           in case xs of
                [] -> F Unit []
                _  -> foldr1 (\x y -> F Mul [x,y]) xs

    fromExp'' :: (Int -> T Sig f' Int Int) -> (Int, Int) -> T Sig f' Int Int
    fromExp'' con (x,n)
        | n < 0     = F Inv [fromExp'' con (x,-n)]
        | otherwise = foldr1 (\_ y -> F Mul [con x,y]) (replicate n (con x))


dom :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
dom []             = Set.empty
dom ((X  x ,_):xs) = Set.insert (X  x ) (dom xs)
dom ((X' x',_):xs) = Set.insert (X' x') (dom xs)

domNotMappingToVar :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
domNotMappingToVar []             = Set.empty
domNotMappingToVar ((_,X  _ ):xs) = domNotMappingToVar xs
domNotMappingToVar ((_,X' _ ):xs) = domNotMappingToVar xs
domNotMappingToVar ((X  x ,_):xs) = Set.insert (X  x ) (domNotMappingToVar xs)
domNotMappingToVar ((X' x',_):xs) = Set.insert (X' x') (domNotMappingToVar xs)

isShared :: TermAlg f f' c x =>
                    T f f' c x -> AGUnifProb f f' c x -> AGUnifProb f f' c x -> Bool
isShared x pe pe'
    = x `member` allVars pe
        &&
      x `member` allVars (filter (\(s,t) -> not (isVar s && isVar t)) pe')


maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return

listT :: Monad m => [a] -> ListT m a
listT = ListT . return

stateT :: Monad m => State s a -> StateT s m a
stateT st = StateT { runStateT = \s -> return (runState st s) }

maybeToListT :: Monad m => Maybe a -> ListT m a
maybeToListT Nothing  = listT []
maybeToListT (Just x) = listT [x]


-- FIXME: unification problems are sets of UNORDERED pairs
-- FIXME: that "numV1" stuff is horrible and slow (find better representation)
-- FIXME: for better performance, only classify newly generated equations
agUnifN
    :: (TermAlg Sig f' Int Int, Show f')
    => AGUnifProb Sig f' Int Int
    -> StateT Int [] (AGUnifProb Sig f' Int Int)
agUnifN p@(classify -> (pe, pe', pi, ph))
    -- VA (variable abstraction)
    | Just ((s,t),ph') <- uncons ph
        = do (s',rs) <- stateT $ homogeneous'' s
             (t',rt) <- stateT $ homogeneous'' t
             agUnifN (pe ++ pe' ++ pi ++ ph' ++ [(s',t')] ++ rs ++ rt)

    -- E-Res
    | (not . inSolvedForm) pe
        = let numV1 = maximum' 0 (map (uncurry max . (numX  *** numX )) pe)
              numV2 = maximum' 0 (map (uncurry max . (numX' *** numX')) pe)
              numC' = maximum' 0 (map (uncurry max . (numC  *** numC )) pe)
           in do ee <- lift . maybeToList $ agUnif1' (map (toExp' numV1 numV2 numC') pe)
                 let qe = fromExp numV1 ee
                 agUnifN (qe ++ pe' ++ pi ++ ph)

    -- E'-Res
    | (not . inSolvedForm) pe'
        = do qe' <- lift . maybeToList $ freeUnif pe'
             agUnifN (pe ++ qe' ++ pi ++ ph)

    -- E-Match    (s in E, t in E'; guaranteed by 'classify')
    | Just ((s,t),pi') <- uncons pi
        = do z <- stateT newV
             let numV1 = max (numX  s) (numX  z)
             let numV2 = max (numX' s) (numX' z)
             let numC' = max (numC  s) (numC  z)
             (fromExp numV1 -> qI) <- lift . maybeToList $
                agConstMatch (toExp numV1 numV2 numC' s) (toExp numV1 numV2 numC' z)
             agUnifN (pe ++ pe' ++ qI ++ [(z,t)] ++ pi' ++ ph)

    -- Merge-E-Match    (P_E and P_E' can both assumed to be solved at this point)
    -- FIXME: in Mem-Init: s in T(F,X)\X; in Merge-E-Match: s in T(F,X)?
    | Just (x,_) <- minView $
                        domNotMappingToVar pe `intersection` domNotMappingToVar pe'
    , ((_,s):pe1,pe2) <- partition ((==x) . fst) pe
        = memRec [((s,x),[x])] (pe1 ++ pe2 ++ pe' ++ pi ++ ph)

    -- Var-Rep          (need to check both possible orientations here!)
    -- FIXME: prefer to eliminate X' over X (already taken care by classify?)
    -- FIXME: allVars is a very expensive computation than can be done incrementally
    --        (e.g. tuple each equation with the variables occurring in that equation)
    |  (((x,y),p'):_) <- forEachWithContext (\(x,y) p' ->
            if
                isVar x && isVar y && x `member` allVars p' && y `member` allVars p'
            then
                if not (isShared x pe pe') || isShared y pe pe' then
                    Just ((x,y), p')
                else if not (isShared y pe pe') || isShared x pe pe' then
                    Just ((y,x), p')
                else
                    Nothing
            else
                Nothing
            ) p
        = agUnifN (map (applySubst [(x,y)] *** applySubst [(x,y)]) p')
        
    -- DONE
    | inSolvedForm p = return p
    | otherwise      = mzero


-- FIXME: propagate failure of agUnif1TreatingAsConstant
memRec
    :: (TermAlg Sig f' Int Int, Show f')
    => [((T Sig f' Int Int, T Sig f' Int Int), [T Sig f' Int Int])]
    -> AGUnifProb Sig f' Int Int
    -> StateT Int [] (AGUnifProb Sig f' Int Int)
memRec [] p
    = agUnifN p
memRec (((s,x),smv):stack) p@(classify -> p'@(pe,pe',pi,ph))
    = do sigma <- lift . maybeToList $ agUnif1TreatingAsConstant smv s x
    
         -- NON-DETERMINISTICALLY (DON'T KNOW) CHOOSE z!
         z <- (lift . toList) (domNotMappingToVar pe')

         let theta  = if z == x then [] else [(z, x)]
         let sigma' = filter (\(x,y) -> not (x `member` domNotMappingToVar pe') && x /= y) sigma
         let ys     = toList $
                        domNotMappingToVar pe' `intersection` domNotMappingToVar sigma
         let pe_sigma_theta = map (applySubst theta *** applySubst theta)
                                (map (applySubst sigma *** applySubst sigma) pe)
         let stack' = map (\y ->
                            ((applySubst theta (applySubst sigma y), applySubst theta y)
                            ,applySubst theta y : smv)
                          ) ys

         memRec (stack' ++ stack) (pe_sigma_theta ++ sigma' ++ theta ++ pe' ++ pi ++ ph)

         
-- STILL TO DO FOR agUnifN:
-- * Simplif
-- * Elim (variable and constant elimination)
-- * Rep (replacement)











