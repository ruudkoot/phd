module LambdaUnion where

-- TODO: make use of the fact that terms are always fully applied
-- TODO: non-deterministic full β-reduction
-- TODO: capture-avoiding substitution
-- TODO: types (kinds)
-- TODO: generate arbitrary (well-typed) terms
-- TODO: test confluence, type preservation, uniqueness of normal forms, etc.
-- TODO: dynamic type checking

import Names

import Data.Maybe (fromJust)
import Data.Set

-- | Expressions

data Sort = C | Sort :=> Sort
    deriving (Eq, Show)

-- TODO: parameterize over a type of constants (single-sorted)
-- TODO: (future work) can we do multi-sorted algebras elegantly with type families?
-- TODO: (future work) generalize over the underlying first-order algebra
data Tm
    = Var Name
    | Abs Name Sort Tm
    | App Tm Tm
    | Union Tm Tm
    | Empty

instance Show Tm where
    show (Var   x    ) = "x" ++ show x
    show (Abs   x s e) = "(λx" ++ show x ++ ":" ++ show s ++ "." ++ show e ++ ")"
    show (App   e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Union e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    show (Empty      ) = "∅"

-- * Syntactic equality up to alpha-renaming

synEqAlpha :: Tm -> Tm -> Bool
synEqAlpha (Var x) (Var x')
    = x == x'
synEqAlpha (Abs x s e) (Abs x' s' e')
    | s == s'   = synEqAlpha e (subst x' (Var x) e')
    -- We can expect that the terms to be compared are of the same sort,
    -- so throw an exception instead of returning False.
    | otherwise = error "synEqAlpha: sort mismatch"
synEqAlpha (App e1 e2) (App e1' e2')
    = synEqAlpha e1 e1' && synEqAlpha e2 e2'
synEqAlpha (Union e1 e2) (Union e1' e2')
    = synEqAlpha e1 e1' && synEqAlpha e2 e2'
synEqAlpha Empty Empty
    = True
synEqAlpha _ _
    = False
    
-- * Free variables

fv :: Tm -> Set Name
fv (Var   x    ) = singleton x
fv (Abs   x k e) = delete x (fv e)
fv (App   e1 e2) = union (fv e1) (fv e2)
fv (Union e1 e2) = union (fv e1) (fv e2)

-- * Substitution

-- FIXME: the ∪-distributivity case in reduce does a tricky substitution which
--        may require α-renaming in order to succeed.
    
subst :: Name -> Tm -> Tm -> Tm
subst x e (Var y)
    | x == y    = e
    | otherwise = Var y
subst x e (Abs y k e')
    | x == y          = Abs y k e'
    -- FIXME: does this catch all captures?
    | y `member` fv e = error "variable captured"
    | otherwise       = Abs y k (subst x e e')
subst x e (App e1 e2)
    = App (subst x e e1) (subst x e e2)
subst x e (Union e1 e2)
    = Union (subst x e e1) (subst x e e2)

-- * Reduction (1-step, top-level)

reduce :: Tm -> Maybe Tm
-- β-reduction
reduce (App (Abs x k e1)  e2)
    = return (subst x e2 e1)
-- FIXME: "∅-reduction": a semi-hack that should be done elsewhere
reduce (App Empty e2)
    = return Empty
-- ∪-reduction
reduce (App (Union e1 e2) e3)
    = return (Union (App e1 e3) (App e2 e3))
-- ∅-unit
reduce (Union Empty e)
    = return e
reduce (Union e Empty)
    = return e
-- ∪-distributivity
reduce (Union (Abs x s e) (Abs x' s' e'))
    | s == s'   = return $ Abs x s (Union e (subst x' (Var x) e')) 
    | otherwise = error "reduce: sort mismatch"
-- ∪-idempotence
reduce (Union (Var x) (Var x'))
    | x == x' = return (Var x)
reduce (Union (Var x) (Union (Var x') e2))
    | x == x' = return (Union (Var x) e2)
-- ∪-congruence(?)
reduce (Union e1 e2)
    | Just x1 <- applicee e1, Just x2 <- applicee e2, x1 == x2
        = return (congrue e1 e2)
reduce (Union e1 (Union e2 e3))
    | Just x1 <- applicee e1, Just x2 <- applicee e2, x1 == x2
        = return (Union (congrue e1 e2) e3)
-- ∪-associativity
reduce (Union (Union e1 e2) e3)
    = return (Union e1 (Union e2 e3))
-- ∪-commutativity
reduce (Union e1 (Union e2 e3))
    | Just x1 <- applicee e1, Just x2 <- applicee e2, x2 < x1
        = return (Union e2 (Union e1 e3))
reduce (Union e1 e2)
    | Just x1 <- applicee e1, Just x2 <- applicee e2, x2 < x1
        = return (Union e2 e1)
reduce _
    = Nothing
    
applicee :: Tm -> Maybe Name
applicee (Var x)     = Just x
applicee (App e1 e2) = applicee e1
applicee _           = Nothing

congrue :: Tm -> Tm -> Tm
congrue (Var x) (Var x')
    | x == x'   = Var x
    | otherwise = error "congrue: variables do not match"
congrue (App e1 e2) (App e1' e2')
    = App (congrue e1 e1') (Union e2 e2')
congrue _ _
    = error "congrue: not an application"

-- * Normalization (full β-reduction)

normalize :: Tm -> Tm
normalize (Var x)
    = Var x
normalize (Abs x k e)
    = Abs x k (normalize e)
normalize (App e1 e2)
    = let e1' = normalize e1
          e2' = normalize e2
       in case reduce (App e1' e2') of
            Just e' -> normalize e'
            Nothing -> App e1' e2'
normalize (Union e1 e2)
    = let e1' = normalize e1
          e2' = normalize e2
       in case reduce (Union e1' e2') of
            Just e' -> normalize e'
            Nothing -> Union e1' e2'
normalize Empty
    = Empty
            
-- * η-expansion

-- TODO: we also need to do "∅-expansion", but we cannot always do this without
--       knowing its sort

type Env = [(Name, Sort)]

etaExpand :: Env -> Tm -> Fresh Tm
etaExpand env (Var x)
    = do etaExpand' x (fromJust $ lookup x env)
etaExpand env (Abs x s e)
    = do e' <- etaExpand ((x,s) : env) e
         return $ Abs x s e'
etaExpand env (App e1 e2)
    = do e1' <- etaExpand env e1
         e2' <- etaExpand env e2
         return $ App e1' e2'
etaExpand env (Union e1 e2)
    = do e1' <- etaExpand env e1
         e2' <- etaExpand env e2
         return $ Union e1' e2'
etaExpand env (Empty)
    = do return $ Empty

etaExpand' :: Name -> Sort -> Fresh Tm
etaExpand' x C           = do return $ Var x
etaExpand' x (s1 :=> s2) = do y <- fresh
                              e <- etaExpand' x s2
                              return (Abs y s1 (App e (Var y)))
