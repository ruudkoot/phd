{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif.FirstOrder.General where

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

import Util

import Unif.FirstOrder.Types
import Unif.FirstOrder.Free            -- FIXME?
import Unif.FirstOrder.AbelianGroups   -- FIXME!

allWithContext :: (a -> [a] -> Bool) -> [a] -> Bool
allWithContext p = and . mapMaybeWithContext (\x ctx -> Just (p x ctx))

-- FIXME: order in which the list elements are fed to 'f' is weird,
-- (but that does not matter if they represent sets)
mapMaybeWithContext :: (a -> [a] -> Maybe b) -> [a] -> [b]
mapMaybeWithContext f = mapMaybeWithContext' []
  where
    mapMaybeWithContext' ys []     = []
    mapMaybeWithContext' ys (x:xs) = case f x (ys ++ xs) of
                            Nothing ->     mapMaybeWithContext' (x : ys) xs
                            Just z  -> z : mapMaybeWithContext' (x : ys) xs


deinterleave :: [a] -> ([a],[a])
deinterleave []       = ([] ,[])
deinterleave [x]      = ([x],[])
deinterleave (x:y:zs) = 
    let (xs,ys) = deinterleave zs
     in (x:xs,y:ys)
     

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)


allAdjacentPairsOnCycle :: (a -> a -> Bool) -> [a] -> Bool
-- allAdjacentPairsOnCycle _ []  = True
-- allAdjacentPairsOnCycle _ [_] = True
allAdjacentPairsOnCycle f xs@(x0:_) = allAdjacentPairsOnCycle' xs
  where
    allAdjacentPairsOnCycle' [xn]            = f xn x0
    allAdjacentPairsOnCycle' (xi:xs'@(xj:_)) = f xi xj && allAdjacentPairsOnCycle' xs'


-- * AG-unification with free function symbols * --------------------------[ ]--

-- Boudet, Jouannaud & Schmidt-Schauß (1989)

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

stateT' :: Monad m => State s1 a -> StateT (s1,s2) m a
stateT' st = StateT {
        runStateT = \(s1,s2) -> let (x, s1') = runState st s1 in return (x, (s1',s2))
    }

log :: (Ord f', Show f', Monad m)
    => Rule f'
    -> (AGUnifProb AG f' () Int)
    -> Set (T AG f' () Int, T AG f' () Int)
    -> StateT (Int, Log f') m (AGUnifProb AG f' () Int)
log l1 (sortBy (compare `on` fst) -> l2@(classify -> (l2c,_))) sc
    = StateT { runStateT = \(s1,s2) -> return (l2,(s1, s2 ++ [LE l1 l2c sc])) }

data Rule f'
    = START
    -- ordinary rules
    | Var_Rep
    | Simplify
    | VA
    | E_Res     { e_resIn             :: AGUnifProb AG f' () Int
                , e_resOut            :: AGUnifProb AG f' () Int
                }
    | E'_Res
    | E_Match
    | Mem_Init  { mem_initX           :: T AG f' () Int
                , mem_initS           :: T AG f' () Int
                , mem_initT           :: T AG f' () Int
                }
    | Mem_Rec   { mem_recGivenStack   :: [((T AG f' () Int, T AG f' () Int)
                                          ,[T AG f' () Int]                  )]
                , mem_recChosenZ      :: T AG f' () Int
                , mem_recChosenZFrom  :: [T AG f' () Int]
                , mem_recAGma        :: [(T AG f' () Int, T AG f' () Int)]
                , mem_recAGma'       :: [(T AG f' () Int, T AG f' () Int)]
                , mem_recTheta        :: [(T AG f' () Int, T AG f' () Int)]
                , mem_recYs           :: [T AG f' () Int]
                , mem_recStack'       :: [((T AG f' () Int, T AG f' () Int)
                                          ,[T AG f' () Int]                  )]
                , mem_recStack''      :: [((T AG f' () Int, T AG f' () Int)
                                          ,[T AG f' () Int]                  )]
                }
    | Elim      { elim_cycles         :: [[(T AG f' () Int, T AG f' () Int)]]
                , elim_chosenPairFrom :: [(T AG f' () Int, T AG f' () Int)]
                , elim_chosenPair     :: (T AG f' () Int, T AG f' () Int)
                , elim_cep            :: AGUnifProb AG f' () Int
                , elim_theta          :: AGUnifProb AG f' () Int
                , elim_cep_theta      :: AGUnifProb AG f' () Int
                , elim_e'inst         :: [T AG f' () Int]
                , elim_sigma          :: AGUnifProb AG f' () Int
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
                      (AGClassifiedUnifProb AG f' () Int)
                      (Set (T AG f' () Int, T AG f' () Int))
  deriving Eq
  
instance Show f' => Show (LogEntry f') where
    show (LE l p sc) = "\n    " ++ show l  ++ "\n        "
                                ++ show p  ++ "\n        "
                                ++ show sc ++ "\n"
    
    
justToList :: Maybe a -> [a]
justToList Nothing  = error "justToList"
justToList (Just x) = [x]


agUnifN
    :: (TermAlg AG f' () Int, Show f')
    => AGUnifProb AG f' () Int
    -> [AGUnifProb AG f' () Int]
agUnifN p =
    let sol = nub (sort (map fst (runStateT (agUnifN' 666 p Set.empty) (0, []))))
     in map replacement sol
     

replacement
    :: TermAlg AG f' () Int
    => AGUnifProb AG f' () Int
    -> AGUnifProb AG f' () Int
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
    :: (TermAlg AG f' () Int, Show f')
    => Int
    -> AGUnifProb AG f' () Int
    -> Set (T AG f' () Int, T AG f' () Int)
    -> StateT (Int, Log f') [] (AGUnifProb AG f' () Int)
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
simplify :: TermAlg AG f' () Int
    =>  AGUnifProb AG f' () Int -> AGUnifProb AG f' () Int
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
    :: (TermAlg AG f' () Int, Show f')
    => Int
    -> [((T AG f' () Int, T AG f' () Int), [T AG f' () Int])]
    -> AGUnifProb AG f' () Int
    -> Set (T AG f' () Int, T AG f' () Int)
    -> StateT (Int, Log f') [] (AGUnifProb AG f' () Int)
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
    :: (TermAlg AG f' () Int, Show f')
    => Int
    -> [((T AG f' () Int, T AG f' () Int), [T AG f' () Int])]
    -> AGUnifProb AG f' () Int
    -> Set (T AG f' () Int, T AG f' () Int)
    -> AGUnifProb AG f' () Int
    -> StateT (Int, Log f') [] (AGUnifProb AG f' () Int)
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

