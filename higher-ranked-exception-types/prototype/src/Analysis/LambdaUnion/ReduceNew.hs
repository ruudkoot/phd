{-# LANGUAGE ViewPatterns #-}

module Analysis.LambdaUnion.ReduceNew (
    toTm',
    normalize'
) where

import Analysis.LambdaUnion.Syntax

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe

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


-- Eta-expand and transform into canonical (but not normalized or canonically
-- ordered) representation.
-- FIXME: return environment extension for freshly generated variables
toTm' :: Ord a => Env -> Tm a -> State Int (Tm' a, Sort)

toTm' env (Var x)
    -- does eta-expansion
    = do let s  = fromJust $ lookup x env
         let ss = sortOfArgs s
         xs <- replicateM (length ss) fresh
         xs' <- map fst <$> mapM (toTm' (zip xs ss ++ env) . Var) xs
         return (Tm' (zip xs ss) [(Var' x, xs')], s)

toTm' env (Con c)
    = return (Tm' [] [(Con' c,[])], C)

toTm' env (Abs x k t)
    = do (Tm' xs ts, s) <- toTm' env t
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
            return (Tm' xs1 (nub $ ts1 ++ map (alphaRename xs2x xs1x) ts2), s1)
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
normalize' :: Ord a => Tm' a -> Tm' a
normalize' t = case normalize'' t of
                    (t', False) -> t'
                    (t', True ) -> normalize' t
  where
    normalize'' :: Ord a => Tm' a -> (Tm' a, Bool)
    normalize'' (Tm' xs ts) | isApplicableBeta   ts
        = undefined
    normalize'' (Tm' xs ts) | isApplicableGamma1 ts
        = undefined
    normalize'' (Tm' xs ts) | isApplicableGamma2 ts
        = undefined
        
    isApplicableBeta :: [(Head a, [Tm' a])] -> Bool
    isApplicableBeta = undefined

    isApplicableGamma1 :: [(Head a, [Tm' a])] -> Bool
    isApplicableGamma1 = undefined

    isApplicableGamma2 :: [(Head a, [Tm' a])] -> Bool
    isApplicableGamma2 ts
        | all isRedex ts, xss <- map getBinders ts
            = True
        | not (any isRedex ts)
            = False
        | otherwise
            = error "isApplicableGamma2"            

    isRedex :: (Head a, [Tm' a]) -> Bool
    isRedex (Redex _, _) = True
    isRedex _            = False
    
    getBinders :: (Head a, [Tm' a]) -> [(Name, Sort)]
    getBinders (Redex (Tm' xs _), _) = xs



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

