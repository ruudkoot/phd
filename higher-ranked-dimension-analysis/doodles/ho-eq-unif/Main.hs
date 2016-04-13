{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ViewPatterns           #-}

module Main where

import Control.Applicative ((<$>))
import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State

import Data.Function
import Data.List (minimumBy, sort)
import Data.Maybe

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set        hiding (filter, foldr, map)
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

-- * AG-unification with free function symbols * --------------------------[ ]--

-- Boudet, Jouannaud & Schmidt-Schauß (1989)

newT :: T f f' x -> State [T f f' x] Int
newT t = do xs' <- get
            modify (++[t])
            return (length xs')

data T f f' x
    = X  x
    | X' Int
    | F  f  [T f f' x]
    | F' f' [T f f' x]
  deriving (Eq, Show)

homogeneous :: T f f' x -> State [T f f' x] (T f f' x)
homogeneous (X  x    ) = return (X  x )
homogeneous (X' x'   ) = return (X' x')
homogeneous (F  f  ts) = F f <$> mapM homogeneous ts
homogeneous (F' f' ts) = X'  <$> newT (F' f' ts)

homogeneous' :: T f f' x -> State [T f f' x] (T f f' x)
homogeneous' (X  x    ) = return (X  x )
homogeneous' (X' x'   ) = return (X' x')
homogeneous' (F  f  ts) = X'    <$> newT (F f ts)
homogeneous' (F' f' ts) = F' f' <$> mapM homogeneous' ts
















