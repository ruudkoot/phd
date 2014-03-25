module Main where

-- TODO: capture-avoiding substitution
-- TODO: types (kinds)
-- TODO: generate arbitrary (well-typed) terms
-- TODO: test confluence, type preservation, uniqueness of normal forms, etc.

import Data.Set

-- | Names

type Name = Int

-- | Expressions

data Tm
    = Var Name
    | Abs Name Tm
    | App Tm Tm
    | Union Tm Tm

instance Show Tm where
    show (Var   x    ) = "x" ++ show x
    show (Abs   x  e ) = "(λx" ++ show x ++ "." ++ show e ++ ")"
    show (App   e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Union e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    
-- * Free variables

fv :: Tm -> Set Name
fv (Var   x    ) = singleton x
fv (Abs   x  e ) = delete x (fv e)
fv (App   e1 e2) = union (fv e1) (fv e2)
fv (Union e1 e2) = union (fv e1) (fv e2)

-- * Substitution
    
subst :: Name -> Tm -> Tm -> Tm
subst x e (Var y)
    | x == y    = e
    | otherwise = Var y
subst x e (Abs y e')
    | x == y          = Abs y e'
    | y `member` fv e = error "variable captured"
    | otherwise       = Abs y (subst x e e')
subst x e (App e1 e2)
    = App (subst x e e1) (subst x e e2)
subst x e (Union e1 e2)
    = Union (subst x e e1) (subst x e e2)
    
-- * Reduction (1-step, top-level)
    
reduce :: Tm -> Maybe Tm
reduce (App (Abs x e1)    e2)   = Just $ subst x e2 e1
reduce (App (Union e1 e2) e3)   = Just $ Union (App e1 e3) (App e2 e3)
reduce (Union (Union e1 e2) e3) = Just $ Union e1 (Union e2 e3)
-- order unions
-- combine arguments
reduce _                        = Nothing

-- * Full β-reduction

fullyReduce :: Tm -> Tm
fullyReduce (Var x)     = Var x
fullyReduce (Abs x e)   = Abs x (fullyReduce e)
fullyReduce (App e1 e2)
    = let e1' = fullyReduce e1
          e2' = fullyReduce e2
       in case reduce (App e1' e2') of
            Just e' -> fullyReduce e'
            Nothing -> App e1' e2'
fullyReduce (Union e1 e2)
    = let e1' = fullyReduce e1
          e2' = fullyReduce e2
       in case reduce (Union e1' e2') of
            Just e' -> fullyReduce e'
            Nothing -> Union e1' e2'
