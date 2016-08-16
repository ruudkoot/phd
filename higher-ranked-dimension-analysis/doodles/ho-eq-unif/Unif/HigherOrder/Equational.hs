{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.HigherOrder.Equational where

import Control.Applicative ((<$>))
import Control.Arrow ((***),(&&&))
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List

import           Data.Function
import           Data.Graph
import           Data.List      ( intersect, minimumBy, nub, partition, sort, sortBy
                                , zip4
                                )
import           Data.Maybe
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Set       hiding (filter, foldr, map, partition, null)
import qualified Data.Set       as Set

import Util

import Unif.FirstOrder.Types

for = flip map

extractFirst :: (a -> Bool) -> [a] -> Maybe (a, [a])
extractFirst p = extractFirst' []
  where
    extractFirst' _   [] = Nothing
    extractFirst' xs' (x:xs)
        | p x       = Just (x, reverse xs' ++ xs)
        | otherwise = extractFirst' (x:xs') xs

statefulForM :: Monad m => s -> [a] -> (s -> a -> m (s, b)) -> m (s, [b])
statefulForM s []     f = return (s, [])
statefulForM s (x:xs) f = do
    (s',  x' ) <- f s x
    (s'', xs') <- statefulForM s' xs f
    return (s'', x' : xs')
    
stateT :: Monad m => State s a -> StateT s m a
stateT st = StateT {
        runStateT = (\s -> let (x, s') = runState st s in return (x, s'))
    }


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
    unify     :: UnificationProblem sort sig
              -> State (Env sort, Env sort)  [Subst sort sig]

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
  
isFlexible :: AlgebraicTerm sort sig -> Bool
isFlexible = isFreeV . hd
  
isRigid :: AlgebraicTerm sort sig -> Bool
isRigid = not . isFlexible

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

    bindAndReduce
        :: Env           sort
        -> Env           sort
        -> Subst         sort sig
        -> AlgebraicTerm sort sig
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


type ConditionalMapping  b s = Map ([SimpleType b], AlgebraicTerm b s)
                                   (AlgebraicTerm b s)
type ConditionalMapping' b s = Map ([SimpleType b], AlgebraicTerm b s) (Atom s)
type OrderReduction      b s = Map (AlgebraicTerm b s) (Atom s)


pmfs
    :: Theory sort sig
    => AlgebraicTerm sort sig
    -> Set ([SimpleType sort], AlgebraicTerm sort sig)
pmfs = pmfs' []
  where
    pmfs' :: Theory sort sig => [SimpleType sort] -> AlgebraicTerm sort sig
                                -> Set ([SimpleType sort], AlgebraicTerm sort sig)
    pmfs' ys (A xs (FreeV f) ss) = singleton (xs ++ ys, A [] (FreeV f) ss)
    pmfs' ys (A xs a         ss) = unionMap' (pmfs' (xs ++ ys)) ss


-- FIXME: merge with applyConditionalMapping
applyConditionalMapping'    -- E-Abs
    :: Theory b s
    => ConditionalMapping' b s
    -> AlgebraicTerm b s
    -> AlgebraicTerm b s
applyConditionalMapping' condMap = applyConditionalMapping'' []
  where
    applyConditionalMapping'' ctx (A xs (FreeV f) ss)
        = case Map.lookup (xs ++ ctx, A [] (FreeV f) ss) condMap of
            Nothing -> A xs (FreeV f) (map (applyConditionalMapping'' (xs ++ ctx)) ss)
            Just a  -> A xs a (map (bound (xs ++ ctx)) [0 .. length (xs ++ ctx) - 1])
    applyConditionalMapping'' ctx (A xs a ss)
        = A xs a (map (applyConditionalMapping'' (xs ++ ctx)) ss)


-- FIXME: merge with applyConditionalMapping'
applyConditionalMapping     -- E-Uni
    :: Theory b s
    => ConditionalMapping b s
    -> AlgebraicTerm b s
    -> AlgebraicTerm b s
applyConditionalMapping condMap = applyConditionalMapping' []
  where
    applyConditionalMapping' ctx (A xs (FreeV f) ss)
        = case Map.lookup (xs ++ ctx, A [] (FreeV f) ss) condMap of
            Nothing ->
                A xs (FreeV f) (map (applyConditionalMapping' (xs ++ ctx)) ss)
            Just (A [] a@(FreeV _) ss') ->
                A xs a (ss' ++ ss)
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

transformAbs
    :: Theory b s
    => HeadConf b s
    -> State (Env b, Env b) (Conf b s)
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
    return $
        ( if length theta' /= unFreeV (head hs) then
            error "transformAbs: assertion failed - substitution too short (or long)"
          else
            theta' ++ for phi (\((xs,A xs' a' ys'),_h) ->
                                    substFreeVAndReduce theta' (A (xs'++xs) a' ys'))
        , [(applyConditionalMapping' phi' u,applyConditionalMapping' phi' v)]
          ++ map (\((xs,A xs' a' ys'),h) -> (atom2term [] envV envC h, A (xs'++xs) a' ys')) phi
          ++ ss
        )
transformAbs _ | otherwise = error "transformAbs: assumptions violated"


-- FIXME: substitutions should be partial?
-- FIXME: don't pollute the environment with temporary variables (Y_i, Z_i)
--        * allocate from separate set of names, as in agUnifN?
-- NOTE: may be non-deterministic if the unification algorithm isn't unary
--       (while AG and BR unification with nullary constants are of unitary type,
--       AG and BR unification with function symbols are finitary!)
transformEUni
    :: Theory sort sig
    => PartConf sort sig
    -> StateT (Env sort, Env sort) [] (Conf sort sig)
transformEUni (theta', ss', ss) | isEAcceptable ss' = do

    -- NOTE: we changed from MFS to PMFS to avoid losing the binders 'bss'
    let (unzip -> (bss, ps)) = toList $ unionMap' (\(u,v) -> pmfs u `union` pmfs v) ss'
    -- check if this didn't increase the cardinality
    let ps' = toList $ Set.map snd (unionMap' (\(u,v) -> pmfs u `union` pmfs v) ss')
    () <- if length ps == length ps' then return () else error "transformEUni: ps / ps'"

    rho <- stateT $ forM ps $ \w -> do
                 t <- typeOfTerm [] w
                 y <- freshAtom t               -- FIXME: FreeV ---> freeV..?
                 return (w,y)

    let rho' = Map.fromList rho

    -- FIXME: applyOrderReduction seems superfluous, just drop the arguments
    --        from G, to obtain Y (or do it in a more straightforward fashion)?
    let rhoSS' = map (applyOrderReduction rho' *** applyOrderReduction rho') ss'
                    -- FIXME: ^ remove duplicates (is a set)

    -- unification may fail or be (in)finitary instead of unitary
    sigmas <- stateT $ unify rhoSS'
    sigma  <- lift sigmas               -- FIXME: not elegant

    let xss    = map (\(A [] _ xs,_) -> xs) rho
    let ys     = map snd rho

    -- FIXME: handle 'us' if not empty
    (_, phis) <- stateT $
        statefulForM [] (zip3 bss xss ys) $ \st (bs_i, xs_i, FreeV y) -> do
            statefulForM st (toList $ pmfs (sigma !! y)) $ \st' (us@[], z) -> do
                case lookup (z, xs_i, us) st' of
                    Nothing -> do
                        tyxs_i <- mapM (typeOfTerm bs_i) xs_i
                        _ :-> t <- typeOfTerm bs_i z
                        z' <- freshAtom (tyxs_i ++ us :-> t)
                        return ( ((z, xs_i, us), z') : st'
                               , ((us, z), A [] z' (xs_i))  -- FIXME: (xs_i ++ us)
                               )                            --     or (us ++ xs_i)
                    Just z' -> do
                        return ( st', ((us, z), A [] z' []) )

    theta <- stateT $ forM (zip4 phis ys bss ps) $
        \(phi, FreeV y, bs_i, A [] (FreeV g) xs) -> do
            ts <- mapM (typeOfTerm bs_i) xs
            let (A us a as) = applyConditionalMapping (Map.fromList phi) (sigma !! y)
            return (g, A (us ++ ts) a as)

    (envV, _) <- get
    let thetaD = map (\(x,y) -> (freeV envV x, y)) theta
    let thetaS = sparsifySubst envV theta

    return $
        ( mergeSubst theta' theta
        , thetaD ++ map (substFreeVAndReduce thetaS *** substFreeVAndReduce thetaS) ss
        )

transformEUni _ | otherwise = error "transformEUni: assumptions violated"


-- FIXME: can't be this easy...
mergeSubst
    :: [AlgebraicTerm sort sig]
    -> [(Int,AlgebraicTerm sort sig)]
    -> [AlgebraicTerm sort sig]
mergeSubst theta' theta =
    let n = length theta'
        m = length theta
     in if map fst theta == [n .. n + m - 1] then
            theta' ++ map snd theta
        else
            error $ "mergeSubst: FAILED"



-- (u,v) assumed to be flexible-rigid (i.e., not rigid-flexible)
-- are we only non-deterministic locally (choice of 'b') or also globally
--                  (choice of '(u,v)')?
-- FIXME: don't cross-pollute the environments of different branches
transformBin
    :: Theory sort sig
    => HeadConf sort sig
    -> StateT (Env sort, Env sort) [] (Conf sort sig)
transformBin (theta', (u@(A xs (FreeV f) us), v@(A _xs a vs)), ss)
  | xs == _xs && isRigid v
    = do (envV, envC) <- get
         ts :-> t <- stateT $ typeOfFreeV f
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
         pbs <- stateT $ mapM (partialBinding (ts :-> t)) bs
         (envV, envC) <- get
         lift $ for pbs $ \pb ->
            let theta = sparsifySubst envV [(f, pb)]
            in ( let (A ys b zs) = theta' !! f
                     theta''     = for zs $ \(A ys' b' zs') -> A (ys' ++ ys) b' zs'
                  in theta' ++ theta''
               , (freeV envV f, pb)
                    : map (substFreeVAndReduce theta *** substFreeVAndReduce theta) ss
               )
transformBin _ = error "transformBin: assumptions violated"


-- * Control strategy (Qian & Wang) * -------------------------------------[ ]--

type ClassifiedTermSystem b s
    = ( TermSystem b s
      , TermSystem b s
      , TermSystem b s
      , TermSystem b s
      )


isTrivialVar :: Theory b s => AlgebraicTerm b s -> Maybe Int
isTrivialVar (A xs (FreeV f) ts)
    | ts == map (bound xs) [0 .. length xs - 1] = Just f
isTrivialVar _ = Nothing


fvTS :: TermSystem b s -> [Int]
fvTS []           = []
fvTS ((t1,t2):ts) = fvAT t1 ++ fvAT t2 ++ fvTS ts

fvAT :: AlgebraicTerm b s -> [Int]
fvAT (A _ (FreeV f) ts) = f : concatMap fvAT ts
fvAT (A _ _         ts) =     concatMap fvAT ts


classifyTermSystem
    :: Theory b s
    => TermSystem b s
    -> TermSystem b s
    -> ClassifiedTermSystem b s
classifyTermSystem _   []     = ([], [], [], [])
classifyTermSystem ts' (t:ts) =
    let (ss_Sol, ss_EUni, ss_FF, ss_Res) = classifyTermSystem (t:ts') ts
     in case t of
            (t1,t2) | Just f <- isTrivialVar t1
                    , f `notElem` fvAT t2 ++ fvTS (ts ++ ts') ->
                ((t1,t2) : ss_Sol, ss_EUni, ss_FF, ss_Res)
            (t1,t2) | Just f <- isTrivialVar t2
                    , f `notElem` fvAT t1 ++ fvTS (ts ++ ts') ->
                ((t2,t1) : ss_Sol, ss_EUni, ss_FF, ss_Res)
            (t1,t2) | let ps = toList $ pmfs t1 `union` pmfs t2
                    , all (uncurry isTrivialFlexibleSubterm) ps ->
                (ss_Sol, (t1,t2) : ss_EUni, ss_FF, ss_Res)
            (t1,t2) | isFlexible t1, isFlexible t2 ->
                (ss_Sol, ss_EUni, (t1,t2) : ss_FF, ss_Res)
            -- orient R-F  -->  F-R
            (t1,t2) | isFlexible t2 ->
                (ss_Sol, ss_EUni, ss_FF, (t2,t1) : ss_Res)
            (t1,t2) ->
                (ss_Sol, ss_EUni, ss_FF, (t1,t2) : ss_Res)


data CSTree b s
    = EAbs
        { eAbs_in       :: (Env b, Env b, Subst b s, ClassifiedTermSystem b s)
        , eAbs_out      :: CSTree b s
        }
    | EUni
        { eUni_in       :: (Env b, Env b, Subst b s, ClassifiedTermSystem b s)
        , eUni_out      :: [CSTree b s]
        }
    | EBin
        { eBin_in       :: (Env b, Env b, Subst b s, ClassifiedTermSystem b s)
        , eBin_out      :: [CSTree b s]
        }
    | CS_Solved
        { solved_Subst  :: Subst b s
        , solved_System :: ClassifiedTermSystem b s     -- FIXME: TermSystem b s?
        }
  deriving Show
  
  
maskCS :: CSTree b s -> CSTree b s
maskCS (EAbs { eAbs_in = (envV, envC, _, cts), eAbs_out })
    = EAbs { eAbs_in = (envV, envC, [], cts), eAbs_out = maskCS eAbs_out }
maskCS (EUni { eUni_in = (envV, envC, _, cts), eUni_out })
    = EUni { eUni_in = (envV, envC, [], cts), eUni_out = map maskCS eUni_out }
maskCS (EBin { eBin_in = (envV, envC, _, cts), eBin_out })
    = EBin { eBin_in = (envV, envC, [], cts), eBin_out = map maskCS eBin_out }
maskCS (CS_Solved { solved_System })
    = CS_Solved { solved_Subst = [], solved_System = solved_System }


-- FIXME: Again, how non-deterministic should we be? Only in so far as the rules
--        themselves are non-deterministic, or also in the choice of equation
--        from the unification problem (for E-Abs and E-Bin)?
-- FIXME: StateT s []  vs. StateT s Identity  uglyness...
controlStrategy
    :: Theory     sort sig
    => (Env sort, Env sort)
    -> Subst      sort sig
    -> TermSystem sort sig
    -> CSTree     sort sig
controlStrategy (envV, envC) theta ss
    = case classifyTermSystem [] ss of
        -- Solved
        cts@(ss_Sol, [], ss_FF, []) ->
            CS_Solved { solved_Subst = theta, solved_System = cts }
        -- Step 1
        -- FIXME: could be more non-deterministic here
        cts@(ss_Sol, ss_EUni, ss_FF, (t1,t2) : ss_Res) ->
            -- FIXME: pass the whole 'ss' or only 'ss_Res' to transformAbs?
            let ((theta', ss'), (envV', envC')) = flip runState (envV, envC) $
                    transformAbs ( theta
                                 , (t1,t2)
                                 , ss_Sol ++ ss_EUni ++ ss_FF ++ ss_Res
                                 )
                csTree = controlStrategy (envV', envV') theta' ss'
             in EAbs { eAbs_in  = (envV, envC, theta, cts)
                     , eAbs_out = csTree
                     }
        -- Step 2 and 3
        cts@(ss_Sol, ss_EUni, ss_FF, []) -> do
            let theta'ss's = flip runStateT (envV, envC) $
                    transformEUni (theta, ss_EUni, ss_Sol ++ ss_FF)
                csTrees = for theta'ss's $ \((theta', ss'), (envV', envC')) ->
                    let cts'@(ss_Sol', [], ss_FF', ss_Res') = classifyTermSystem [] ss'
                    -- FIXME: could be more non-deterministic here
                    in case
                         extractFirst (\(t1,t2) -> isRigid t1 && isRigid t2) ss_Res'
                       of
                        Just ((t1,t2), ss_Res'') ->
                            let theta''ss''s = flip runStateT (envV', envC') $
                                    transformBin ( theta
                                                 , (t1,t2)
                                                 , ss_Sol' ++ ss_FF ++ ss_Res''
                                                 )
                                csTrees = for theta''ss''s $
                                    \((theta'', ss''), (envV'', envC'')) ->
                                        controlStrategy (envV'', envC'') theta'' ss''
                            in EBin { eBin_in  = (envV', envC', theta', cts')
                                    , eBin_out = csTrees
                                    }
                        Nothing -> controlStrategy
                                        (envV', envV')
                                        theta'
                                        (ss_Sol' ++ ss_FF' ++ ss_Res')
             in EUni { eUni_in  = (envV, envC, theta, cts)
                     , eUni_out = csTrees
                     }


breadthFirstSearchForSolutions
    :: [CSTree sort sig]
    -> ([(Subst sort sig, ClassifiedTermSystem sort sig)], [CSTree sort sig])
breadthFirstSearchForSolutions [] = ([],[])
breadthFirstSearchForSolutions (EAbs { eAbs_out } : csTrees)
    = breadthFirstSearchForSolutions (csTrees ++ [eAbs_out])
breadthFirstSearchForSolutions (EUni { eUni_out } : csTrees)
    = breadthFirstSearchForSolutions (csTrees ++ eUni_out)
breadthFirstSearchForSolutions (EBin { eBin_out } : csTrees)
    = breadthFirstSearchForSolutions (csTrees ++ eBin_out)
breadthFirstSearchForSolutions (CS_Solved { solved_Subst, solved_System } : csTrees)
    = let (sols, csTrees') = breadthFirstSearchForSolutions csTrees
       in ((solved_Subst, solved_System) : sols, csTrees')


higherOrderEquationalPreunification
    :: Theory sort sig
    => Env sort
    -> Env sort
    -> TermSystem sort sig
    -> [(Subst sort sig, TermSystem sort sig, TermSystem sort sig)]
higherOrderEquationalPreunification envV envC ts
    -- FIXME: do lazy pattern-matching
    = let (sols, []) = breadthFirstSearchForSolutions
                            [controlStrategy (envV, envC) [] ts]
       in map (\(theta,(ssSol, [], ssFF, [])) -> (theta, ssSol, ssFF)) sols


-- | Conversion between HO and FO | --------------------------------------------

data F' sort
    = L  Int (SimpleType sort)   -- lambda
    | B  Int (SimpleType sort)   -- bound
    | FC Int                     -- free constant
  deriving (Eq, Ord, Show)

-- p. 407
firstOrderify
    :: UnificationProblem sort sig
    -> FOUnifProb sig (F' sort) () Int
firstOrderify = map (firstOrderify' [] *** firstOrderify' [])

  where

    firstOrderify'
        :: [(Int, SimpleType sort)]
        -> AlgebraicTerm sort sig
        -> T sig (F' sort) () Int
    firstOrderify' ns (A xs a ts) =
        let ns' = zip [length ns .. ] xs
            xs' = foldr (\(i,t) r -> F' (L i t) [r]) a' ns'
            a'  = firstOrderifyAtom (ns' ++ ns) a ts'
            ts' = map (firstOrderify' (ns' ++ ns)) ts
         in xs'

    firstOrderifyAtom
        :: [(Int, SimpleType sort)]
        -> Atom sig
        -> [T sig (F' sort) () Int]
        -> T sig (F' sort) () Int
    firstOrderifyAtom ns (Bound n) ts = let (i,ty) = ns !! n in F' (B i ty) []
    firstOrderifyAtom _  (FreeV n) ts = X n
    firstOrderifyAtom _  (FreeC n) ts = F' (FC n) ts
    firstOrderifyAtom _  (Const f) ts = F f ts


solvedAGUnifProbToSubst
    :: forall sort sig
     . FOUnifProb sig (F' sort) () Int
    -> State (Env sort, Env sort) (Subst sort sig)
solvedAGUnifProbToSubst p = do

    (envV, envC) <- get    

    let upd r n t
          | length r < n = r ++ map (freeV envV) [length r .. n - 1] ++ [t]
          -- | length r < n = r ++ map (\x -> error $ "upd: " ++ show x) [length r .. n - 1] ++ [t]
          | otherwise    = take n r ++ [t] ++ drop (n + 1) r

    let fo2ho :: [SimpleType sort] -> T sig (F' sort) () Int -> AlgebraicTerm sort sig
        fo2ho env (X  x    ) = freeV envV x
        fo2ho env (X' x'   ) = error "fo2ho: X'"
        fo2ho env (C  c    ) = error "fo2ho: C"
        fo2ho env (F  f  ts) = A [] (Const f) (map (fo2ho env) ts)
        fo2ho env (F' (L n ty) ts)
            = error "fo2ho: F' L"
        fo2ho env (F' (B n ty) ts)
            = bound (replicate n (error "fo2ho: B") ++ [ty]) n
        fo2ho env (F' (FC n) ts)
            = error "fo2ho: F' FC"

    return $ foldr (\(X n, t) r -> upd r n (fo2ho [] t)) [] p
    
unify'
    :: (TermAlg sig (F' sort) () Int, Show (F' sort))
    => (FOUnifProb sig (F' sort) () Int -> [FOUnifProb sig (F' sort) () Int])
    -> UnificationProblem sort sig
    -> State (Env sort, Env sort) [Subst sort sig]
unify' foUnifN p = do
    let p'     = firstOrderify p
    let sigmas = foUnifN p'
    mapM solvedAGUnifProbToSubst sigmas
