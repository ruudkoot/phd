module Analysis.LambdaUnionOld.Syntax (
    module Analysis.Names,
    Env,
    Sort(..),
    Tm(..),
    fv,
    maxName,
    subst
) where

import Data.Set

import Analysis.Names

-- | Types

type Env = [(Name, Sort)]

data Sort = C | Sort :=> Sort
    deriving (Eq, Read, Show)

-- TODO: (future work) can we do multi-sorted algebras elegantly with type families?
-- TODO: (future work) generalize over the underlying first-order algebra
data Tm a
    = Var Name
    | Con a
    | Abs Name Sort (Tm a)
    | App (Tm a) (Tm a)
    | Union (Tm a) (Tm a)
    | Empty
    deriving Read
    
instance Show a => Show (Tm a) where        -- FIXME: move to Print (needs Types
    show (Var   x    ) = "x" ++ show x      --        to avoid cyclic imports)
    show (Con   c    ) = "{" ++ show c ++ "}"
    show (Abs   x s e) = "(λx" ++ show x ++ ":" ++ show s ++ "." ++ show e ++ ")"
    show (App   e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Union e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    show (Empty      ) = "∅"
   
-- | Free variables

fv :: Tm a -> Set Name
fv (Var   x    ) = singleton x
fv (Con   c    ) = empty
fv (Abs   x k e) = delete x (fv e)
fv (App   e1 e2) = union (fv e1) (fv e2)
fv (Union e1 e2) = union (fv e1) (fv e2)
fv (Empty      ) = empty

-- FIXME: 0 might not be the least element of Name
maxName :: Tm a -> Name
maxName (Var   x    ) = x
maxName (Con   c    ) = 0
maxName (Abs   x k e) = maxName e
maxName (App   e1 e2) = max (maxName e1) (maxName e2)
maxName (Union e1 e2) = max (maxName e1) (maxName e2)
maxName (Empty      ) = 0

-- | Substitution

-- FIXME: the ∪-distributivity case in reduce does a tricky substitution which
--        may require α-renaming in order to succeed.
    
subst :: Name -> Tm a -> Tm a -> Tm a
subst x e (Var y)
    | x == y    = e
    | otherwise = Var y
subst x e (Con c)
    = Con c
subst x e (Abs y k e')
    | x == y          = Abs y k e'
    -- FIXME: does this catch all captures?
    | y `member` fv e = error "variable captured"
    | otherwise       = Abs y k (subst x e e')
subst x e (App e1 e2)
    = App (subst x e e1) (subst x e e2)
subst x e (Union e1 e2)
    = Union (subst x e e1) (subst x e e2)
subst x e Empty
    = Empty
