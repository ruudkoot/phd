module Analysis.LambdaUnion.ReduceNew (
    normalize
) where

import Analysis.LambdaUnion.Syntax

import Data.List

data Head a = Var' Name | Con' a | Redex (Tm' a)
  deriving (Eq, Show)

data Tm' a = Tm' [(Name,Sort)] [(Head a,[Tm' a])]
  deriving (Eq, Show)

toTm' :: Ord a => Env -> Tm a -> Tm' a
toTm' env (Var x)
    -- FIXME: eta-expand (needs environment!)
    = Tm' [] [(Var' x,[])]
toTm' env (Con c)
    = Tm' [] [(Con' c,[])]
toTm' env (Abs x k t)
    = let Tm' xs ts = toTm' env t
       in Tm' ((x,k):xs) ts
toTm' env (App t1 t2)
    = let t1' = toTm' env t1
          t2' = toTm' env t2
            -- FIXME: case-split on head here
       in Tm' [] [(Redex t1',[t2'])]
toTm' env (Union t1 t2) -- FIXME: need to do some alpha-renaming
    = let Tm' xs1 ts1 = toTm' env t1
          Tm' xs2 ts2 = toTm' env t2
       in if xs1 == xs2 then
            Tm' xs1 (nub $ ts1 ++ ts2)
          else
            error "toTm': Union"
toTm' env Empty
    = Tm' [] []


normalize :: Ord a => Tm a -> Tm a
normalize = undefined

