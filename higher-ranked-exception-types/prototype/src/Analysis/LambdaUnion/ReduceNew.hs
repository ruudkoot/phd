{-# LANGUAGE ViewPatterns #-}

module Analysis.LambdaUnion.ReduceNew (
    toTm',
    fromTm',
    normalize'
) where

import Analysis.LambdaUnion.Syntax

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Data.Function
import Data.List
import Data.Maybe

-- FIXME: Redex [Tm' a] or ([Head a],[Tm' a])?

data Head a = Var' Name | Con' a | Redex (Tm' a)
  deriving (Eq, Show)

data Tm' a = Tm' [(Name,Sort)] [(Head a,[Tm' a])]
  deriving (Eq, Show)


alphaRename :: [Name] -> [Name] -> (Head a, [Tm' a]) -> (Head a, [Tm' a])
alphaRename xs ys (f, ts) = (alphaRenameF f, map alphaRenameT ts)
  where
    alphaRenameF (Var' x)
        = case elemIndex x xs of
            Nothing -> Var' x
            Just n  -> Var' (ys !! n)
    alphaRenameF (Con' c)
        = Con' c
    alphaRenameF (Redex t)
        = Redex (alphaRenameT t)

    alphaRenameT (Tm' xs'@(unzip -> (xs'x,_)) ts')
        = if xs `intersect` xs'x == [] && ys `intersect` xs'x == [] then
            Tm' xs' (map (alphaRename xs ys) ts')
          else
            error "alphaRenameF"
            

synEqUpToAlphaK :: Eq a => (Head a, [Tm' a]) -> (Head a, [Tm' a]) -> Bool
synEqUpToAlphaK (f, ts) (f', ts')
    = synEqUpToAlphaF f f' && length ts == length ts'
        && and (zipWith synEqUpToAlphaT ts ts')
  where
    synEqUpToAlphaF :: Eq a => Head a -> Head a -> Bool
    synEqUpToAlphaF (Var'  x) (Var'  y) = x == y
    synEqUpToAlphaF (Con'  c) (Con'  d) = c == d
    synEqUpToAlphaF (Redex t) (Redex u) = synEqUpToAlphaT t u
    synEqUpToAlphaF _         _         = False

    synEqUpToAlphaT :: Eq a => Tm' a -> Tm' a -> Bool
    synEqUpToAlphaT (Tm' (unzip -> (xs,ss)) ts) (Tm' (unzip -> (xs', ss')) ts')
        | ss == ss', length ts == length ts'
            = and (zipWith synEqUpToAlphaK ts (map (alphaRename xs' xs) ts'))
        | otherwise
            = False


nubUpToAlpha :: Eq a => [(Head a, [Tm' a])] -> [(Head a, [Tm' a])]
nubUpToAlpha = nubBy synEqUpToAlphaK


-- Eta-expand and transform into canonical (but not normalized or canonically
-- ordered) representation.
-- FIXME: return environment extension for freshly generated variables
toTm' :: Ord a => Env -> Tm a -> State Int (Tm' a, Sort)

toTm' env (Var x)
    -- does eta-expansion
    = do let s  = case lookup x env of
                    Just s  -> s
                    Nothing -> error $ "toTm'(Var): x = " ++ show x
                                            ++ "; env = " ++ show env
         let ss = sortOfArgs s
         xs <- replicateM (length ss) fresh
         xs' <- map fst <$> mapM (toTm' (zip xs ss ++ env) . Var) xs
         return (Tm' (zip xs ss) [(Var' x, xs')], s)

toTm' env (Con c)
    = return (Tm' [] [(Con' c,[])], C)

toTm' env (Abs x k t)
    = do (Tm' xs ts, s) <- toTm' ((x,k):env) t
         case lookup x xs of
            Just _  -> error "toTm': Abs"
            Nothing -> return (Tm' ((x,k):xs) ts, k :=> s)

toTm' env (App t1 t2)
    -- applies one argument and eta-expands
    = do (tm'1, s1) <- toTm' env t1
         (tm'2, s2) <- toTm' env t2

         let (s2':ss) = sortOfArgs s1
         xs <- replicateM (length ss) fresh
         xs' <- map fst <$> mapM (toTm' (zip xs ss ++ env) . Var) xs

         if s2 == s2' then
            return (Tm' (zip xs ss) [(Redex tm'1, tm'2 : xs')], argsToSort ss)
         else
            error "toTm': App"

toTm' env (Union t1 t2)
    = do (Tm' xs1@(unzip -> (xs1x,xs1k)) ts1, s1) <- toTm' env t1
         (Tm' xs2@(unzip -> (xs2x,xs2k)) ts2, s2) <- toTm' env t2
         -- FIXME: need to do some alpha-renaming
         if s1 == s2 && xs1k == xs2k then
            return (Tm' xs1 (nubUpToAlpha $ ts1 ++ map (alphaRename xs2x xs1x) ts2), s1)
         else
            error "toTm': Union"

toTm' env Empty
    -- FIXME: always of sort C? (eiher add a sort parameter or make sure it is)
    = return (Tm' [] [], C)


-- Convert a cononical (but not necesarily normalized or canonically ordered)
-- representation into an ordinary term.
fromTm' :: Tm' a -> Tm a
fromTm' (Tm' xs ts)
    = absFrom xs (unionFrom (map fromTm'' ts))
  where
    etaContract :: Tm a -> Tm a
    etaContract (Abs x k (App t (Var x'))) | x == x'
        = t
    etaContract t = t
  
    absFrom :: [(Name,Sort)] -> Tm a -> Tm a
    absFrom [] t'         = t'
    absFrom ((x,k):xs) t' = etaContract (Abs x k (absFrom xs t'))
    
    unionFrom :: [Tm a] -> Tm a
    unionFrom []     = Empty
    unionFrom [t]    = t
    unionFrom (t:ts) = Union t (unionFrom ts)
    
    applyArgs :: Tm a -> [Tm a] -> Tm a
    applyArgs t' []     = t'
    applyArgs t' (t:ts) = applyArgs (App t' t) ts
    
    fromTm'' :: (Head a, [Tm' a]) -> Tm a
    fromTm'' (f, ts) =
        let args = map fromTm' ts
         in case f of
                Var'  x -> Var     x `applyArgs` args
                Con'  c -> Con     c `applyArgs` args
                Redex t -> fromTm' t `applyArgs` args


-- Check if a term is in normal (but not necesarily canonically ordered) form.
isNf' :: Tm' a -> Bool
isNf' (Tm' xs ts) = all isNf'' ts
  where
    isNf'' (Var' _, ts') = all isNf' ts'
    isNf'' (Con' _, ts') = all isNf' ts'
    isNf'' (_     , _  ) = False


-- Reduce a canonical representation into a normalized and canonically ordered
-- form.
normalize' :: (Eq a, Ord a, Show a) => Tm' a -> Tm' a
normalize' t
    = let t' = normalize'' t
       in if t == t' then
            canonicallyOrder t
          else
            normalize' t'
  where
    normalize'' :: (Eq a, Ord a, Show a) => Tm' a -> Tm' a
    
    -- R-Beta + R-Gamma1
    normalize'' (Tm' xs ks)
        | let ks' = nubUpToAlpha $ concatMap betaReduce ks
        , ks /= ks'
        = Tm' xs ks'
            where
              betaReduce :: (Head a,[Tm' a]) -> [(Head a,[Tm' a])]
              betaReduce k@(Redex (Tm' xs ks), ts)
                = map (subst (map fst xs) ts) ks
              betaReduce k
                = [k]
              
              subst :: [Name] -> [Tm' a] -> (Head a, [Tm' a]) -> (Head a, [Tm' a])
              subst xs ts (f, ts') = (substF xs ts f, map (substT xs ts) ts')
              
              substF :: [Name] -> [Tm' a] -> Head a -> Head a
              substF xs ts (Var'  x)
                | Just n <- elemIndex x xs = Redex (ts !! n)   -- new redex!
                | otherwise                = Var' x
              substF xs ts (Con'  c) = Con' c
              substF xs ts (Redex t) = Redex (substT xs ts t)
              
              substT :: [Name] -> [Tm' a] -> Tm' a -> Tm' a
              substT xs ts (Tm' xs' ks)
                | not (null (xs `intersect` (map fst xs'))) = error "substT"
                | otherwise
                    = Tm' xs' (map (subst xs ts) ks)

    -- R-Gamma2
    normalize'' (Tm' xs ks@((Redex (Tm' xs' _),_):_))
        | isApplicableGamma2 ks, length xs' >= 1
            = Tm' (xs ++ xs') (map unbind ks)
                where
                    unbind :: (Head a, [Tm' a]) -> (Head a, [Tm' a])
                    unbind (Redex (Tm' xs' ts), ts')
                        = (Redex (Tm' [] (map ar ts)), ts')
                    ar = alphaRename (map fst xs) (map fst xs')
                    
    -- RECURSE
    normalize'' (Tm' xs ks)
        = Tm' xs (nubUpToAlpha $ map (normalizeF'' *** map normalize'') ks)
            where
              normalizeF'' :: (Eq a, Ord a, Show a) => Head a -> Head a
              normalizeF'' (Var'  x) = Var'  x
              normalizeF'' (Con'  c) = Con'  c
              normalizeF'' (Redex t) = Redex (normalize'' t)

    isApplicableGamma2 :: Show a => [(Head a, [Tm' a])] -> Bool
    isApplicableGamma2 ks
        | all isRedex ks                                -- all redices
        , (xs@(length->n):xss) <- map getBinders ks     -- at least one rexed
        , n >= 1                                        -- at least one binder
        , all ((==n) . length) xss                      -- sanity check
            = True
        | not (any isRedex ks)
            = False
        | otherwise
            = error $ "isApplicableGamma2: " ++ show ks

    isRedex :: (Head a, [Tm' a]) -> Bool
    isRedex (Redex _, _) = True
    isRedex _            = False

    getBinders :: (Head a, [Tm' a]) -> [(Name, Sort)]
    getBinders (Redex (Tm' xs _), _) = xs


-- Canonically order a normal form.
canonicallyOrder :: (Ord a, Show a) => Tm' a -> Tm' a
canonicallyOrder (Tm' xs ks)
    = let ks'       = map (canonicallyOrderF *** map canonicallyOrder) ks
          orderedKs = sortBy compareK ks'
       in Tm' xs orderedKs
            where
              canonicallyOrderF :: (Ord a, Show a) => Head a -> Head a
              canonicallyOrderF (Var'  x) = Var'  x
              canonicallyOrderF (Con'  c) = Con'  c
              canonicallyOrderF (Redex t) = Redex (canonicallyOrder t)

              -- arguments assumed to have been ordered by an earlier recursive call!
              -- normal form, so this case analysis is complete
              compareK :: (Ord a, Show a) => (Head a, [Tm' a]) -> (Head a, [Tm' a]) -> Ordering
              compareK (Con' c, ts) (Con' d, ts') = case compare c d of
                                                        LT -> LT
                                                        GT -> GT
                                                        EQ -> compareTS ts ts'
              compareK (Con' _, _ ) (Var' _, _  ) = LT
              compareK (Var' _, _ ) (Con' _, _  ) = GT
              compareK (Var' x, ts) (Var' y, ts') = case compare x y of
                                                        LT -> LT
                                                        GT -> GT
                                                        EQ -> compareTS ts ts'

              compareKS :: (Ord a, Show a) => [(Head a, [Tm' a])] -> [(Head a, [Tm' a])] -> Ordering
              compareKS []     []       = EQ
              compareKS []     _        = LT                -- this can occur!
              compareKS _      []       = GT                -- this can occur!
              compareKS (k:ks) (k':ks') = case compareK k k' of
                                            LT -> LT
                                            GT -> GT
                                            EQ -> compareKS ks ks'
              
              -- assumed to have been ordered by an earlier recursive call!
              compareT :: (Ord a, Show a) => Tm' a -> Tm' a -> Ordering
              compareT (Tm' xs ts) (Tm' xs' ts')
                = compareKS ts ts'
                
              compareTS :: (Ord a, Show a) => [Tm' a] -> [Tm' a] -> Ordering
              compareTS []     []       = EQ                -- will get nubbed!
              compareTS []     _        = LT                -- FIXME: should not occur
              compareTS _      []       = GT                -- FIXME: should not occur
              compareTS (t:ts) (t':ts') = case compareT t t' of
                                            LT -> LT
                                            GT -> GT
                                            EQ -> compareTS ts ts'
                                            


-- | TESTS | -------------------------------------------------------------------

test_toTm'_1 =
    let env = [(0,C:=>(C:=>C))]
        tm  = App (Var 0) (Con "l")
     in runState (toTm' env tm) 100
            ==
        ((Tm' [(102,C)] [(Redex (Tm' [(100,C),(101,C)] [(Var' 0,[Tm' [] [(Var' 100,[])],Tm' [] [(Var' 101,[])]])]),[Tm' [] [(Con' "l",[])],Tm' [] [(Var' 102,[])]])],C :=> C),103)
        
test_fromTm'_1 =
    let env = [(0,C:=>(C:=>C))]
        tm  = App (Var 0) (Con "l")
        tm' = fst (fst (runState (toTm' env tm) 100))
     in fromTm' tm'

test_isNf'_1 = 
    let env = [(0,C:=>(C:=>C))]
        tm  = App (Var 0) (Con "l")
        tm' = fst (fst (runState (toTm' env tm) 100))
     in isNf' tm'
            ==
        False

test_normalize'_0 =
    let env = [(0,C:=>(C:=>C))]
        tm  = App (Var 0) (Con "l")
        tm' = fst (fst (runState (toTm' env tm) 100))
     in tm'

test_normalize'_1 =
    let env = [(0,C:=>(C:=>C))]
        tm  = App (Var 0) (Con "l")
        tm' = fst (fst (runState (toTm' env tm) 100))
     in normalize' tm'
     
test_normalize'_2 =
    let tm' = Tm' [(102,C)] [(Redex (Tm' [] [(Var' 0,[Tm' [] [(Redex (Tm' [] [(Con' "l",[])]),[])],Tm' [] [(Redex (Tm' [] [(Var' 102,[])]),[])]])]),[])]
     in normalize' tm'
