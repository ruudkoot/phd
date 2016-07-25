{-------------------------------------------------------------------------------

    STILL TO DO FOR agUnifN:
    * implement Elim properly
      * occur-check?
    * FIXME (e.g. Simplify)
    * Mem-Rec has been "fixed"(?) w.r.t. Boudet et al.

    SANITY CHECKING:
    * of unification results
    
-------------------------------------------------------------------------------}

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif where

import Prelude hiding (log)

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


-- | Utility | ------------------------------------------------------------[ ]--

assert :: String -> Bool -> Bool
assert ss True  = True
assert ss False = error $ "ASSERT: " ++ ss

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

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

maximum' :: Ord a => a -> [a] -> a
maximum' x xs = maximum (x : xs)

deinterleave :: [a] -> ([a],[a])
deinterleave []       = ([] ,[])
deinterleave [x]      = ([x],[])
deinterleave (x:y:zs) = 
    let (xs,ys) = deinterleave zs
     in (x:xs,y:ys)
     
-- FIXME: order in which the list elements are fed to 'f' is weird,
-- (but that does not matter if they represent sets)
mapMaybeWithContext :: (a -> [a] -> Maybe b) -> [a] -> [b]
mapMaybeWithContext f = mapMaybeWithContext' []
  where
    mapMaybeWithContext' ys []     = []
    mapMaybeWithContext' ys (x:xs) = case f x (ys ++ xs) of
                            Nothing ->     mapMaybeWithContext' (x : ys) xs
                            Just z  -> z : mapMaybeWithContext' (x : ys) xs
                            
allWithContext :: (a -> [a] -> Bool) -> [a] -> Bool
allWithContext p = and . mapMaybeWithContext (\x ctx -> Just (p x ctx))

allAdjacentPairsOnCycle :: (a -> a -> Bool) -> [a] -> Bool
-- allAdjacentPairsOnCycle _ []  = True
-- allAdjacentPairsOnCycle _ [_] = True
allAdjacentPairsOnCycle f xs@(x0:_) = allAdjacentPairsOnCycle' xs
  where
    allAdjacentPairsOnCycle' [xn]            = f xn x0
    allAdjacentPairsOnCycle' (xi:xs'@(xj:_)) = f xi xj && allAdjacentPairsOnCycle' xs'

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
        ( error "TODO"
        , thetaD ++ map (substFreeVAndReduce thetaS *** substFreeVAndReduce thetaS) ss
        )

transformEUni _ | otherwise = error "transformEUni: assumptions violated"


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


isTrivialVar :: Theory b s => AlgebraicTerm b s -> Bool
isTrivialVar (A xs (FreeV _) ts)
    | ts == map (bound xs) [0 .. length xs - 1] = True
isTrivialVar _ = False


classifyTermSystem
    :: Theory b s
    => TermSystem b s
    -> ClassifiedTermSystem b s
classifyTermSystem []     = ([], [], [], [])
classifyTermSystem (t:ts) =
    let (ss_Sol, ss_EUni, ss_FF, ss_Res) = classifyTermSystem ts
     in case t of
            (t1,t2) | isTrivialVar t1 ->
                ((t1,t2) : ss_Sol, ss_EUni, ss_FF, ss_Res)
            (t1,t2) | isTrivialVar t2 ->
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
        , solved_System :: ClassifiedTermSystem b s
        }
  deriving Show


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
    = case classifyTermSystem ss of
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
                    let cts'@(ss_Sol', [], ss_FF', ss_Res') = classifyTermSystem ss'
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

unify'
    :: UnificationProblem Sort Sig
    -> State (Env Sort, Env Sort) [Subst Sort Sig]
unify' p = do
    let p'     = firstOrderify p
    let sigmas = agUnifN p'
    mapM solvedAGUnifProbToSubst sigmas

data F'
    = L  Int (SimpleType Sort)   -- lambda
    | B  Int (SimpleType Sort)   -- bound
    | FC Int                     -- free constant
  deriving (Eq, Ord, Show)

-- p. 407
firstOrderify
    :: UnificationProblem Sort Sig
    -> AGUnifProb Sig F' () Int
firstOrderify = map (firstOrderify' [] *** firstOrderify' [])

  where

    firstOrderify'
        :: [(Int, SimpleType Sort)]
        -> AlgebraicTerm Sort Sig
        -> T Sig F' () Int
    firstOrderify' ns (A xs a ts) =
        let ns' = zip [length ns .. ] xs
            xs' = foldr (\(i,t) r -> F' (L i t) [r]) a' ns'
            a'  = firstOrderifyAtom (ns' ++ ns) a ts'
            ts' = map (firstOrderify' (ns' ++ ns)) ts
         in xs'

    firstOrderifyAtom
        :: [(Int, SimpleType Sort)]
        -> Atom Sig
        -> [T Sig F' () Int]
        -> T Sig F' () Int
    firstOrderifyAtom ns (Bound n) ts = let (i,ty) = ns !! n in F' (B i ty) []
    firstOrderifyAtom _  (FreeV n) ts = X n
    firstOrderifyAtom _  (FreeC n) ts = F' (FC n) ts
    firstOrderifyAtom _  (Const f) ts = F f ts


solvedAGUnifProbToSubst
    :: AGUnifProb Sig F' () Int
    -> State (Env Sort, Env Sort) (Subst Sort Sig)
solvedAGUnifProbToSubst p = do

    (envV, envC) <- get    

    let upd r n t
          | length r < n = r ++ map (freeV envV) [length r .. n - 1] ++ [t]
          -- | length r < n = r ++ map (\x -> error $ "upd: " ++ show x) [length r .. n - 1] ++ [t]
          | otherwise    = take n r ++ [t] ++ drop (n + 1) r

    let fo2ho :: [SimpleType Sort] -> T Sig F' () Int -> AlgebraicTerm Sort Sig
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

-- Solve a system of equations in AG, while treating a set of given variables as
-- constants.
agUnif1TreatingAsConstant
    :: TermAlg Sig f' () Int
    => [T Sig f' () Int]               -- set of marked variables SMV
    -> AGUnifProb Sig f' () Int
    -> Maybe (AGUnifProb Sig f' () Int)
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
    :: TermAlg Sig f' Int Int
    => Int
    -> [T Sig f' () Int]
    -> T Sig f' () Int
    -> T Sig f' Int Int
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
    :: TermAlg Sig f' Int Int
    => Int
    -> T Sig f' Int Int
    -> T Sig f' () Int
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

-- * AG-unification with free function symbols * --------------------------[ ]--

-- Boudet, Jouannaud & Schmidt-Schauß (1989)

-- FIXME: instead of X and X': x --> Either x Int?
-- FIXME: combine C and F?
data T f f' c x
    = X  x                  -- variables            (E and E')
    | X' Int                -- fresh variables      (E and E')
    | C  c                  -- nullary constants    (FIXME: E???)
    | F  f  [T f f' c x]    -- function symbols     (E)
    | F' f' [T f f' c x]    -- function symbols     (E')
  deriving (Eq, Ord, Show)

type AGUnifProb f f' c x = [(T f f' c x, T f f' c x)]
  
class    (Ord  f, Ord  f', Ord  c, Ord  x
         ,Show f, Show f', Show c, Show x) => TermAlg f f' c x
instance (Ord f, Ord f', Ord c, Ord x
         ,Show f, Show f', Show c, Show x) => TermAlg f f' c x

newT :: T f f' c x -> State (Int, AGUnifProb f f' c x) Int
newT t = do (n, xs') <- get
            modify (\(n, xs') -> (n+1, xs' ++ [(X' n,t)]))     -- performance...
            return n
            
newV :: State Int (T f f' c x)
newV = do n <- get
          modify (+1)
          return (X' n)

isX :: T f f' x c -> Bool
isX (X _) = True
isX _     = False

isX' :: T f f' x c -> Bool
isX' (X' _) = True
isX' _      = False

isVar :: T f f' x c -> Bool
isVar (X  _) = True
isVar (X' _) = True
isVar _      = False

vars :: T f f' c x -> [x]
vars (X  x   ) = [x]
vars (X' _   ) = []
vars (C  _   ) = error "vars: C" -- []
vars (F  _ ts) = concatMap vars ts
vars (F' _ ts) = concatMap vars ts

vars' :: T f f' c x -> [Int]
vars' (X  _   ) = []
vars' (X' x   ) = [x]
vars' (C  _   ) = error "vars': C" -- []
vars' (F  _ ts) = concatMap vars' ts
vars' (F' _ ts) = concatMap vars' ts

allVars :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
allVars = unionMap' (\(s,t) -> allVars' s `union` allVars' t)

allVars' :: TermAlg f f' c x => T f f' c x -> Set (T f f' c x)
allVars' t@(X  _   ) = singleton t
allVars' t@(X' _   ) = singleton t
allVars'   (C  _   ) = error "allVars': C" -- empty
allVars'   (F  _ ts) = unionMap' allVars' ts
allVars'   (F' _ ts) = unionMap' allVars' ts    

homogeneous :: T f f' c x -> State (Int, AGUnifProb f f' c x) (T f f' c x)
homogeneous (X  x    ) = return (X  x )
homogeneous (X' x'   ) = return (X' x')
homogeneous (C  c    ) = error "homogeneous: C" -- return (C  c )
homogeneous (F  f  ts) = F f <$> mapM homogeneous ts
homogeneous (F' f' ts) = X'  <$> newT (F' f' ts)

homogeneous' :: T f f' c x -> State (Int, AGUnifProb f f' c x) (T f f' c x)
homogeneous' (X  x    ) = return (X  x )
homogeneous' (X' x'   ) = return (X' x')
homogeneous' (C  c    ) = error "homogeneous': C" -- X'    <$> newT (C c)
homogeneous' (F  f  ts) = X'    <$> newT (F f ts)
homogeneous' (F' f' ts) = F' f' <$> mapM homogeneous' ts

homogeneous'' :: T f f' c x -> State Int (T f f' c x, AGUnifProb f f' c x)
homogeneous'' (X  x   ) = return (X  x , [])
homogeneous'' (X' x'  ) = return (X' x', [])
homogeneous'' (C  c   ) = error "homogeneous'': C" -- return (C  c , [])
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
isPureE (C  _   ) = error "isPureE: C" -- True
isPureE (F  _ ts) = all isPureE ts
isPureE (F' _ _ ) = False

isPureE' :: T f f' c x -> Bool
isPureE' (X  _   ) = True
isPureE' (X' _   ) = True
isPureE' (C  _   ) = error "isPureE': C" -- False
isPureE' (F  _ _ ) = False
isPureE' (F' _ ts) = all isPureE' ts

isHeterogeneous :: T f f' c x -> Bool
isHeterogeneous t = let ((_,rs),_) = runState (homogeneous'' t) 0 in not (null rs)

subst :: TermAlg f f' c x => x -> T f f' c x -> T f f' c x -> T f f' c x
subst x t t'@(X  x') | x == x'   = t
                     | otherwise = t'
subst x _ t'@(X' _ ) = t'
subst x _ t'@(C  _ ) = error "subst: C" -- t'
subst x t (F  f  ts) = F  f  (map (subst x t) ts)
subst x t (F' f' ts) = F' f' (map (subst x t) ts)

subst' :: Int -> T f f' c x -> T f f' c x -> T f f' c x
subst' _ _ t'@(X  _ ) = t'
subst' x t t'@(X' x') | x == x'   = t
                      | otherwise = t'
subst' _ _ t'@(C  _ ) = error "subst': C" -- t'
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
applySubst sigma (C c     ) = error "applySubst: C" -- C c
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


-- FIXME: orient equations with variable on the rhs!
classify
    :: TermAlg f f' c x
    => AGUnifProb f f' c x
    -> (AGClassifiedUnifProb f f' c x, AGUnifProb f f' c x)
classify p = let (pe,pe',pi,ph) = classify' p in ((pe,pe',pi,ph),pe++pe'++pi++ph)
  where
    classify' [] = ([],[],[],[])
    classify' ((orient -> p@(s,t)):ps)
        = let (pe,pe',pi,ph) = classify' ps
           in case p of
                -- remove useless equations
                (X  x , X  y)  | x  == y
                    -> (pe, pe', pi, ph)
                (X' x', X' y') | x' == y'
                    -> (pe, pe', pi, ph)
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
                _ -> error "classify': should not happen"
orient (s,t)
    | not (isVar s), isVar t = (t,s)
    | otherwise              = (s,t)


-- Definition 1
inSolvedForm :: TermAlg f f' c x => AGUnifProb f f' c x -> Bool
inSolvedForm p
    = let domain = dom p
          range  = ran p
       in all inSolvedForm' p
            && length p == Set.size (Set.fromList (map fst p))
            && Set.null (domain `intersection` range)
  where inSolvedForm' (X  _, _) = True
        inSolvedForm' (X' _, _) = True
        inSolvedForm' _         = False
        
-- Definition 2 (Cannot check soundness and completeness!)
isCSU :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x) -> Bool
isCSU p w = inSolvedForm p
                && dom p `isSubsetOf` w
                && Set.null (img p `intersection` w)

-- Definition 8
inSeparatedForm :: TermAlg f f' c x => AGUnifProb f f' c x -> Bool
inSeparatedForm (classify -> ((pe, pe', [], []),p))
    = inSolvedForm pe && inSolvedForm pe'
        && (flip all) pe (\p -> case p of
            (X  x , _) -> (flip all) pe' (\p' -> case p' of
                (X y, t) | x == y -> isVar t
                (t, X y) | x == y -> isVar t
                _                 -> True
              )
            (X' x', _) -> (flip all) pe' (\p' -> case p' of
                (X' y', t) | x' == y' -> isVar t
                (t, X' y') | x' == y' -> isVar t
                _                     -> True
              )
            _          -> True
           )
        && (flip allWithContext) pe' (\(x,y) ctx ->
                if isVar x && isVar y then
                    let vs = allVars (pe ++ ctx)
                     in x `notMember` vs || y `notMember` vs
                else
                    True
              )
inSeparatedForm _
    = False

numX :: T f f' c Int -> Int
numX (X  x   ) = x + 1
numX (X' _   ) = 0
numX (C  _   ) = error "numX: C" -- 0
numX (F  _ ts) = maximum' 0 (map numX ts)
numX (F' _ ts) = maximum' 0 (map numX ts)

numX' :: T f f' c x -> Int
numX' (X  _   ) = 0
numX' (X' x'  ) = x' + 1
numX' (C  _   ) = error "numX': C" -- 0
numX' (F  _ ts) = maximum' 0 (map numX' ts)
numX' (F' _ ts) = maximum' 0 (map numX' ts)

numC :: T f f' Int x -> Int
numC (X  _   ) = 0
numC (X' _   ) = 0
numC (C  c   ) = c + 1
numC (F  _ ts) = maximum' 0 (map numC ts)
numC (F' _ ts) = maximum' 0 (map numC ts)

castC :: T f f' () x -> T f f' c x
castC (X  x    ) = X  x
castC (X' x'   ) = X' x'
castC (C  c    ) = error "castC: C"
castC (F  f  ts) = F  f  (map castC ts)
castC (F' f' ts) = F' f' (map castC ts)

castC' :: T f f' c x -> T f f' () x
castC' (X  x    ) = X  x
castC' (X' x'   ) = X' x'
castC' (C  c    ) = error "castC': C"
castC' (F  f  ts) = F  f  (map castC' ts)
castC' (F' f' ts) = F' f' (map castC' ts)

toExp :: Int -> Int -> Int -> T Sig f' () Int -> AGExp1
toExp v1 v2 c s = toExp' v1 v2 c (castC s, F Unit [])

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
dom []                            = Set.empty
dom ((X  x ,X  y ):_ ) | x  == y  = error "dom: X"
dom ((X' x',X' y'):_ ) | x' == y' = error "dom: X'"
dom ((X  x ,_    ):xs)            = Set.insert (X  x ) (dom xs)
dom ((X' x',_    ):xs)            = Set.insert (X' x') (dom xs)

domNotMappingToVar :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
domNotMappingToVar []             = Set.empty
domNotMappingToVar ((_,X  _ ):xs) = domNotMappingToVar xs
domNotMappingToVar ((_,X' _ ):xs) = domNotMappingToVar xs
domNotMappingToVar ((X  x ,_):xs) = Set.insert (X  x ) (domNotMappingToVar xs)
domNotMappingToVar ((X' x',_):xs) = Set.insert (X' x') (domNotMappingToVar xs)

ran :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
ran subst = unions (map ran' subst)
  where
    domain = dom subst
    ran' (X  x , t) | X  x  `member` domain = allVars' t
                    | otherwise             = Set.empty
    ran' (X' x', t) | X' x' `member` domain = allVars' t
                    | otherwise             = Set.empty

img :: TermAlg f f' c x => AGUnifProb f f' c x -> Set (T f f' c x)
img = unions . map (allVars' . snd)

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
stateT st = StateT {
        runStateT = (\s -> let (x, s') = runState st s in return (x, s'))
    }

stateT' :: Monad m => State s1 a -> StateT (s1,s2) m a
stateT' st = StateT {
        runStateT = \(s1,s2) -> let (x, s1') = runState st s1 in return (x, (s1',s2))
    }

log :: (Ord f', Show f', Monad m)
    => Rule f'
    -> (AGUnifProb Sig f' () Int)
    -> Set (T Sig f' () Int, T Sig f' () Int)
    -> StateT (Int, Log f') m (AGUnifProb Sig f' () Int)
log l1 (sortBy (compare `on` fst) -> l2@(classify -> (l2c,_))) sc
    = StateT { runStateT = \(s1,s2) -> return (l2,(s1, s2 ++ [LE l1 l2c sc])) }

data Rule f'
    = START
    -- ordinary rules
    | Var_Rep
    | Simplify
    | VA
    | E_Res     { e_resIn             :: AGUnifProb Sig f' () Int
                , e_resOut            :: AGUnifProb Sig f' () Int
                }
    | E'_Res
    | E_Match
    | Mem_Init  { mem_initX           :: T Sig f' () Int
                , mem_initS           :: T Sig f' () Int
                , mem_initT           :: T Sig f' () Int
                }
    | Mem_Rec   { mem_recGivenStack   :: [((T Sig f' () Int, T Sig f' () Int)
                                          ,[T Sig f' () Int]                  )]
                , mem_recChosenZ      :: T Sig f' () Int
                , mem_recChosenZFrom  :: [T Sig f' () Int]
                , mem_recSigma        :: [(T Sig f' () Int, T Sig f' () Int)]
                , mem_recSigma'       :: [(T Sig f' () Int, T Sig f' () Int)]
                , mem_recTheta        :: [(T Sig f' () Int, T Sig f' () Int)]
                , mem_recYs           :: [T Sig f' () Int]
                , mem_recStack'       :: [((T Sig f' () Int, T Sig f' () Int)
                                          ,[T Sig f' () Int]                  )]
                , mem_recStack''      :: [((T Sig f' () Int, T Sig f' () Int)
                                          ,[T Sig f' () Int]                  )]
                }
    | Elim      { elim_cycles         :: [[(T Sig f' () Int, T Sig f' () Int)]]
                , elim_chosenPairFrom :: [(T Sig f' () Int, T Sig f' () Int)]
                , elim_chosenPair     :: (T Sig f' () Int, T Sig f' () Int)
                , elim_cep            :: AGUnifProb Sig f' () Int
                , elim_theta          :: AGUnifProb Sig f' () Int
                , elim_cep_theta      :: AGUnifProb Sig f' () Int
                , elim_e'inst         :: [T Sig f' () Int]
                , elim_sigma          :: AGUnifProb Sig f' () Int
                }
    | Rep
    -- failure/success conditions
    | OUT_OF_FUEL
    | E'_Unification_Failure
    | MemRec_Unification_Failure
    | FAILED
    | SOLVED
  deriving (Eq, Show)

type Log      f' = [LogEntry f']
data LogEntry f' = LE (Rule f')
                      (AGClassifiedUnifProb Sig f' () Int)
                      (Set (T Sig f' () Int, T Sig f' () Int))
  deriving Eq
  
instance Show f' => Show (LogEntry f') where
    show (LE l p sc) = "\n    " ++ show l  ++ "\n        "
                                ++ show p  ++ "\n        "
                                ++ show sc ++ "\n"
    
    
justToList :: Maybe a -> [a]
justToList Nothing  = error "justToList"
justToList (Just x) = [x]


agUnifN
    :: (TermAlg Sig f' () Int, Show f')
    => AGUnifProb Sig f' () Int
    -> [AGUnifProb Sig f' () Int]
agUnifN p =
    let sol = nub (sort (map fst (runStateT (agUnifN' 666 p Set.empty) (0, []))))
     in map replacement sol
     

replacement
    :: TermAlg Sig f' () Int
    => AGUnifProb Sig f' () Int
    -> AGUnifProb Sig f' () Int
replacement p
    = let p' = replacement' p
       in if p == p' then filter originalVarsOnly p else replacement p'
  where
    -- Rep
    -- FIXME: side-conditions
    replacement' p
      | (q:qs) <- mapMaybeWithContext (\(x,s) p -> case (x,s) of
                    (x,s) | isVar x, x `member` allVars p
                       -> Just
                            ((x,s) : map (applySubst [(x,s)] *** applySubst [(x,s)]) p)
                    _  -> Nothing
                  ) p
          = q
      | otherwise = p
      
    originalVarsOnly q@(X _, _) = True
    originalVarsOnly _          = False


-- FIXME: not all equations get oriented in all rules (fail to call 'classify')
-- FIXME: unification problems are sets of UNORDERED pairs
-- FIXME: that "numV1" stuff is horrible and slow (find better representation)
-- FIXME: for better performance, only classify newly generated equations
-- FIXME: for better performance, treat non-determinism as a DAG instead of tree
--        (especially for Elim)
agUnifN'
    :: (TermAlg Sig f' () Int, Show f')
    => Int
    -> AGUnifProb Sig f' () Int
    -> Set (T Sig f' () Int, T Sig f' () Int)
    -> StateT (Int, Log f') [] (AGUnifProb Sig f' () Int)
agUnifN' fuel _p@(classify -> ((pe, pe', pi, ph),p)) sc
    | fuel <= 0 = error "agUnifN': OUT_OF_FUEL" -- log OUT_OF_FUEL p sc
    | _p /= p = agUnifN' (fuel - 1) p sc
    -- Var-Rep          (need to check both possible orientations here!)
    -- FIXME: prefer to eliminate X' over X (already taken care by classify?)
    -- FIXME: allVars is a very expensive computation than can be done incrementally
    --        (e.g. tuple each equation with the variables occurring in that equation)
    |  (((x,y),p'):_) <- mapMaybeWithContext (\(x,y) p' ->
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
        = do p'' <- log Var_Rep  (map (applySubst [(x,y)] *** applySubst [(x,y)]) p') sc
             agUnifN' (fuel - 1) p'' sc

    -- Simplify
    | p /= simplify p
        = do p' <- log Simplify (simplify p) sc
             agUnifN' (fuel - 1) p' sc

    -- VA (variable abstraction)
    | Just ((s,t),ph') <- uncons ph
        = do (s',rs) <- stateT' $ homogeneous'' s
             (t',rt) <- stateT' $ homogeneous'' t
             p' <- log VA (pe ++ pe' ++ pi ++ ph' ++ [(s',t')] ++ rs ++ rt) sc
             agUnifN' (fuel - 1) p' sc

    -- E-Res
    | not (inSolvedForm pe)
        = let numV1 = maximum' 0 (map (uncurry max . (numX  *** numX )) pe)
              numV2 = maximum' 0 (map (uncurry max . (numX' *** numX')) pe)
              numC' = 0 -- maximum' 0 (map (uncurry max . (numC  *** numC )) pe)
           in do ee <- lift . justToList $
                    agUnif1' (map (toExp' numV1 numV2 numC' . (castC *** castC)) pe)
                 let qe = map (castC' *** castC') (fromExp numV1 ee)
                 p' <- log (E_Res pe qe) (qe ++ pe' ++ pi ++ ph) sc
                 agUnifN' (fuel - 1) p' sc

    -- E'-Res
    | not (inSolvedForm pe')
        = case freeUnif pe' of
                Just qe' -> do p' <- log E'_Res (pe ++ qe' ++ pi ++ ph) sc
                               agUnifN' (fuel - 1) p' sc
                Nothing  -> -- mzero
                            log E'_Unification_Failure p sc

    -- E-Match    (s in E, t in E'; guaranteed by 'classify')
    | Just ((s,t),pi') <- uncons pi
        = do z <- stateT' newV
             let numV1 = max (numX  s) (numX  z)
             let numV2 = max (numX' s) (numX' z)
             let numC' = 0 -- max (numC  s) (numC  z)
             (map (castC' *** castC') . fromExp numV1 -> qI) <- lift . justToList $
                agConstMatch (toExp numV1 numV2 numC' s) (toExp numV1 numV2 numC' z)
             p' <- log E_Match (pe ++ pe' ++ qI ++ [(z,t)] ++ pi' ++ ph) sc
             agUnifN' (fuel - 1) p' sc

    -- Merge-E-Match    (P_E and P_E' can both assumed to be solved at this point)
    -- FIXME: in Mem-Init: s in T(F,X)\X; in Merge-E-Match: s in T(F,X)?
    | Just (x,_) <- minView $
                        domNotMappingToVar pe `intersection` domNotMappingToVar pe'
    , ((_,s):pe1,pe2) <- partition ((==x) . fst) pe
        = do let ((_,t):_,_) = partition ((==x) . fst) pe'      -- DUMMY / DEBUG ONLY!
             p' <- log (Mem_Init x s t) (pe1 ++ pe2 ++ pe' ++ pi ++ ph) sc
             memRec fuel [((s,x),[x])] p' sc
    -- Elim
    | inSeparatedForm p
    , cs@(_:_) <- findCycles p
        = if all validCycle cs then

            do error $ "agUnifN' (Elim): valid cycle " ++ show cs
            

               -- choose a pair to eliminate (non-deterministically)
               -- FIXME: too non-deterministic?
               -- FIXME: what if all pairs are already in SC?
               c <- lift cs
               let n = length c `div` 2
               let getPair i = (fst (c !! (2 * (i - 1))), fst (c !! (2 * (i - 1) + 1))) 
               let is = [ i | i <- [1 .. n], getPair i `notMember` sc]
               i <- lift is
               let (xi, xj) = getPair i

{-
               -- choose a pair to eliminate (deterministically)
               let ((xi, xj):_) = [ pair
                                  | c <- cs
                                  , let n = length c `div` 2
                                  , i <- [1 .. n]
                                  , let pair =
                                            ( fst (c !! (2 * (i - 1)    ))
                                            , fst (c !! (2 * (i - 1) + 1)) ) 
                                  , pair `notMember` sc
                                  ]
-}
               -- formulate and solve the associated constant elimination problem(s)
               let sc' = (xi, xj) `insert` sc
               let cep = constantEliminationProblem sc' pe
               theta <- lift $ variableIdentifications cep
               let cep_theta = map (applySubst theta *** applySubst theta) cep
               let e'inst    = nub (sort (map fst (filter (isPureE' . snd) cep_theta)))
               sigma <- lift . justToList $ agUnif1TreatingAsConstant e'inst cep_theta
               
               -- finish up
               p' <- log (Elim { elim_cycles         = cs
                               , elim_chosenPairFrom = map getPair is
                               , elim_chosenPair     = (xi, xj)
                               , elim_cep            = cep
                               , elim_theta          = theta
                               , elim_cep_theta      = cep_theta
                               , elim_e'inst         = e'inst
                               , elim_sigma          = sigma
                               })
                         (map (applySubst sigma *** applySubst sigma) pe
                                ++ theta ++ pe' ++ sigma)
                         sc'
               agUnifN' (fuel - 1) p' sc'

          else error $ "agUnifN' (Elim): invalid cycle " ++ show cs
    -- DONE
    | inSeparatedForm p = log SOLVED p sc
    | otherwise         = error "agUnifN': FAILED" -- log FAILED p sc


{- helpers for Elim -----------------------------------------------------------}

constantEliminationProblem
    :: TermAlg f f' c x
    => Set (T f f' c x, T f f' c x)
    -> AGUnifProb f f' c x
    -> AGUnifProb f f' c x
constantEliminationProblem sc pe
    = [ (xk,s) | (xk,yk) <- toList sc, (_,s) <- filter ((== yk) . fst) pe]

selectionWithReplacement :: Int -> [a] -> [[a]]
selectionWithReplacement 0 _  = [[]]
selectionWithReplacement n xs
    = [ y : ys | y <- xs, ys <- selectionWithReplacement (n-1) xs ]

variableIdentifications
    :: TermAlg f f' c x
    => AGUnifProb f f' c x
    -> [AGUnifProb f f' c x]
variableIdentifications cep
    = let ys = nub (sort (map fst (filter (isPureE' . snd) cep)))
       in [ zip ys ts | ts <- selectionWithReplacement (length ys) ys ]

{------------------------------------------------------------------------------}

{- cycle detection ------------------------------------------------------------}

isCyclicSCC :: SCC a -> Bool
isCyclicSCC (AcyclicSCC _) = False
isCyclicSCC (CyclicSCC  _) = True

unCyclicSCC :: SCC a -> [a]
unCyclicSCC (CyclicSCC xs) = xs

-- FIXME: this doesn't detect reflexive cycles (but those shouldn't be relevant,
--        all the cycles should be of even lenght)
findCycles :: TermAlg f f' c x => AGUnifProb f f' c x -> [[(T f f' c x, T f f' c x)]]
findCycles p =
    let graph  = map (\(x,t) -> ((x,t), x, toList $ allVars' t)) p
        sccs   = stronglyConnComp graph
        cycles = filter isCyclicSCC sccs
     in map (rotateCycle . unCyclicSCC) cycles
     
-- Rotates a cycle so it is of the form E', E, ..., E', E.
rotateCycle :: [(T f f' c x, T f f' c x)] -> [(T f f' c x, T f f' c x)]
rotateCycle cs@((x,t):cs')
    | isPureE  t = cs' ++ [(x,t)]
    | isPureE' t = cs

validCycle :: TermAlg f f' c x => [(T f f' c x, T f f' c x)] -> Bool
validCycle c =
    let (e's, es) = deinterleave c
     in even (length c)
            && all (not . isVar . snd) e's && all (isPureE' . snd) e's
            && all (not . isVar . snd) es  && all (isPureE  . snd) es
            && allAdjacentPairsOnCycle (\(_,t) (x,_) -> x `member` allVars' t) c

{------------------------------------------------------------------------------}


-- FIXME: This is not a faithful implementation of "remove equations of the form
--        v=t where v is a variable that was not in the original problem (X')
--        and v occurs nowhere else in P and t is not a variable of the original
--        problem (X), or t occurs somewhere else in P. (However that last part
--        is supposed to be read...)
simplify :: TermAlg Sig f' () Int
    =>  AGUnifProb Sig f' () Int -> AGUnifProb Sig f' () Int
simplify ps
    | ps == simplify' [] ps = ps
    | otherwise             = simplify (simplify' [] ps)
  where
    simplify' qs []
        = qs
    simplify' qs ((X' v,t):ps)
        | X' v `notMember` unions [allVars qs, allVars ps]
            = simplify' qs ps
    simplify' qs (p:ps)
        = simplify' (qs ++ [p]) ps


memRec
    :: (TermAlg Sig f' () Int, Show f')
    => Int
    -> [((T Sig f' () Int, T Sig f' () Int), [T Sig f' () Int])]
    -> AGUnifProb Sig f' () Int
    -> Set (T Sig f' () Int, T Sig f' () Int)
    -> StateT (Int, Log f') [] (AGUnifProb Sig f' () Int)
memRec 0 _ p sc
    = log OUT_OF_FUEL p sc
memRec fuel [] p sc
    = agUnifN' (fuel - 1) p sc
memRec fuel gs@(((s,x),smv):stack) (classify -> ((pe,pe',pi,ph),p)) sc
    = case agUnif1TreatingAsConstant smv [(s,x)] of
            Just sigma -> memRec' fuel gs p sc sigma
            Nothing    -> -- mzero 
                          log MemRec_Unification_Failure p sc

memRec'
    :: (TermAlg Sig f' () Int, Show f')
    => Int
    -> [((T Sig f' () Int, T Sig f' () Int), [T Sig f' () Int])]
    -> AGUnifProb Sig f' () Int
    -> Set (T Sig f' () Int, T Sig f' () Int)
    -> AGUnifProb Sig f' () Int
    -> StateT (Int, Log f') [] (AGUnifProb Sig f' () Int)
memRec' fuel gs@(((s,x),smv):stack) (classify -> ((pe,pe',pi,ph),p)) sc sigma
    = do -- NON-DETERMINISTICALLY (DON'T KNOW) CHOOSE z!
         let z' = toList (domNotMappingToVar pe')
         z <- lift z'

         let theta  = if z == x then [] else [(z, x)]


         {- FIXME: how to interpret the paper's sigma'? -----------------------}

         let sigma' =
         
         -- "sigma is applied to P_E, and the equivalent equations are added to P"
         -- (may have too many equations, so may not be complete)

                sigma


         -- Jur's interpretation (looks to be complete and correct)
         -- (we possibly lose an equation, so may not be correct)

            --  filter (\(x,y) -> x /= z && x /= y) sigma


         -- "sigma' is the restriction to non-E'-instantiated variables"
         -- seems complete, but definitly not correct

            --  filter (\(x,y) -> x `notMember` domNotMappingToVar pe' && x /= y) sigma

         {---------------------------------------------------------------------}



         let ys     = toList $
                        domNotMappingToVar pe' `intersection` domNotMappingToVar sigma
         let pe_sigma_theta = map (applySubst theta *** applySubst theta)
                                (map (applySubst sigma *** applySubst sigma) pe)
         let stack' = map
                (\y -> ((applySubst theta (applySubst sigma y), applySubst theta y)
                       ,applySubst theta y : smv)
                ) ys
         let stack'' = map
                (\((s,x),smv) -> ((applySubst theta (applySubst sigma s)
                                  ,applySubst theta (applySubst sigma x))
                                 -- smv are constants, so sigma is idempotent
                                 --                       theta is not?
                                 ,map (applySubst theta) smv)
                ) stack
         p' <- log (Mem_Rec gs z z' sigma sigma' theta ys stack' stack'')
                   (pe_sigma_theta ++ sigma' ++ theta ++ pe' ++ pi ++ ph)
                   sc
         memRec (fuel - 1) (stack' ++ stack'') p' sc

