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
            return (Tm' (zip xs ss) [(Redex tm'2, tm'1 : xs')], argsToSort ss)
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

-- Reduce a canonical representation into a normalized and canonically ordered
-- form.
normalize' :: Ord a => Tm' a -> Tm' a
normalize' = undefined

