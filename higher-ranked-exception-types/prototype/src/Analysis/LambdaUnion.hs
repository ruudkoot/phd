module Analysis.LambdaUnion where

-- TODO: make use of the fact that terms are always fully applied
-- TODO: non-deterministic full β-reduction
-- TODO: capture-avoiding substitution
-- TODO: types (kinds)
-- TODO: generate arbitrary (well-typed) terms
-- TODO: test confluence, type preservation, uniqueness of normal forms, etc.
-- TODO: dynamic type checking

import Analysis.Names

import Data.Set
import GHC.Exts (sortWith)

import Analysis.Latex

-- | Expressions

data Sort = C | Sort :=> Sort
    deriving (Eq, Read, Show)

instance Latex Sort where
    latex C           = "C"
    latex (s1 :=> s2) = "(" ++ latex s1 ++ "\\Rightarrow " ++ latex s2 ++ ")"

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

instance Show a => Show (Tm a) where
    show (Var   x    ) = "x" ++ show x
    show (Con   c    ) = "{" ++ show c ++ "}"
    show (Abs   x s e) = "(λx" ++ show x ++ ":" ++ show s ++ "." ++ show e ++ ")"
    show (App   e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Union e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    show (Empty      ) = "∅"

instance Latex a => Latex (Tm a) where
    latex (Var   x    )
        = "x_{" ++ show x ++ "}"
    latex (Con   c    )
        = "\\{" ++ latex c ++ "\\}"
    latex (Abs   x s e)
        = "(\\lambda x_{" ++ show x ++ "}:" ++ latex s ++ "." ++ latex e ++ ")"
    latex (App   e1 e2) 
        = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (Union e1 e2)
        = "(" ++ latex e1 ++ "\\cup" ++ latex e2 ++ ")"
    latex (Empty      )
        = "\\emptyset"

-- * Syntactic equality up to alpha-renaming

synEqAlpha :: Eq a => Tm a -> Tm a -> Bool
synEqAlpha (Var x) (Var x')
    = x == x'
synEqAlpha (Con c) (Con c')
    = c == c'
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

fv :: Tm a -> Set Name
fv (Var   x    ) = singleton x
fv (Con   c    ) = empty
fv (Abs   x k e) = delete x (fv e)
fv (App   e1 e2) = union (fv e1) (fv e2)
fv (Union e1 e2) = union (fv e1) (fv e2)

-- FIXME: 0 might not be the least element of Name
maxName :: Tm a -> Name
maxName (Var   x    ) = x
maxName (Con   c    ) = 0
maxName (Abs   x k e) = maxName e
maxName (App   e1 e2) = max (maxName e1) (maxName e2)
maxName (Union e1 e2) = max (maxName e1) (maxName e2)
maxName (Empty      ) = 0

-- * Substitution

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

-- * Reduction (1-step, top-level)

-- TODO: do dynamic type checking (needs a completely type-annotated syntax tree)
-- TODO: do any rules rely on the order of matching?

reduce :: Ord a => Tm a -> Maybe (Tm a)
-- β-reduction
reduce (App (Abs x k e1) e2)
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
reduce (Union (Con c) (Con c'))
    | c == c' = return (Con c)
reduce (Union (Var x) (Union (Var x') e))
    | x == x' = return (Union (Var x) e)
reduce (Union (Con c) (Union (Con c') e))
    | c == c' = return (Union (Con c) e)
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
-- ∪-commutativity ("ordering of variables and constants")
reduce (Union e1 (Union e2 e3))
    | Just x1 <- applicee e1, Just x2 <- applicee e2, x2 < x1
        = return (Union e2 (Union e1 e3))
reduce (Union e1 e2)
    | Just x1 <- applicee e1, Just x2 <- applicee e2, x2 < x1
        = return (Union e2 e1)
reduce (Union (Con c1) (Union (Con c2) e3))
    | c2 < c1 = return (Union (Con c2) (Union (Con c1) e3))
reduce (Union (Con c1) (Con c2))
    | c2 < c1 = return (Union (Con c2) (Con c1))
reduce (Union e1 (Union (Con c2) e3))
    | Just x1 <- applicee e1
        = return (Union (Con c2) (Union e1 e3))
reduce (Union e1 (Con c2))
    | Just x1 <- applicee e1
        = return (Union (Con c2) e1)
-- no rules where applicable..
reduce _
    = Nothing
    
applicee :: Tm a -> Maybe Name
applicee (Var x)     = Just x
applicee (App e1 e2) = applicee e1
applicee _           = Nothing

congrue :: Tm a -> Tm a -> Tm a
congrue (Var x) (Var x')
    | x == x'   = Var x
    | otherwise = error "congrue: variables do not match"
congrue (App e1 e2) (App e1' e2')
    = App (congrue e1 e1') (Union e2 e2')
congrue _ _
    = error "congrue: not an application"

-- * Normalization (full β-reduction)

normalize :: Ord a => Tm a -> Tm a
normalize (Var x)
    = Var x
normalize (Con c)
    = Con c
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

-- TODO: we also need to do "∅-expansion" (or better: generate correct terms in
--       the solver), but we cannot always do this without knowing its sort;
--       instead there currently is a small hack in reduce

type Env = [(Name, Sort)]

etaExpand :: Env -> Tm a -> Fresh (Tm a)
etaExpand env (Var x)
    = do etaExpand' x (lookup' "etaExpand" x env)
etaExpand env (Con c)
    = do return (Con c)
etaExpand env (Abs x s e)
    = do e' <- etaExpand ((x,s) : env) e
         return (Abs x s e')
etaExpand env (App e1 e2)
    = do e1' <- etaExpand env e1
         e2' <- etaExpand env e2
         return (App e1' e2')
etaExpand env (Union e1 e2)
    = do e1' <- etaExpand env e1
         e2' <- etaExpand env e2
         return (Union e1' e2')
etaExpand env (Empty)
    = do return (Empty)

etaExpand' :: Name -> Sort -> Fresh (Tm a)
etaExpand' x C
    = do return (Var x)
etaExpand' x (s1 :=> s2)
    = do y <- fresh
         e <- etaExpand' x s2
         return (Abs y s1 (App e (Var y)))

-- * Semantic equality

-- TODO: infer sorts of free variables?
-- NOTE: in this case the environments for e1 and e2 should be equal in a REGULAR theory
-- NOTE: the effects (generating fresh variables) can never escape and are masked;
--       alternatively: move η-expansion out of this function
-- NOTE: η-expansion is very aggressive, but β-reduction undoes the damage;
--       alternatively, we could 1) do η-expansion on-the-fly as a reduction rule, or
--       2) alter the syntax to keep all expressions in fully applied form

semanticallyEqual :: Ord a => Env -> Tm a -> Tm a -> Bool
semanticallyEqual env e1 e2 =
    let e1'  = evalFresh (etaExpand env e1) (maxName e1 + 1001)
        e2'  = evalFresh (etaExpand env e2) (maxName e2 + 1001)
     in synEqAlpha (normalize e1') (normalize e2')
