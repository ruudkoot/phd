module Analysis.LambdaUnion.Reduce (
    normalize,
    etaExpand
) where

import Analysis.LambdaUnion.Syntax

-- | Reduction (1-step, top-level)

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
-- ∪-congruence(?) [WIDENING!] [NEEDED FOR MAP, WHY? NOT FOR RISERS?]
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

-- | Normalization (full β-reduction)

(#) :: (b -> a) -> b -> (a, b)
x # y = (x y, y)

normalize' :: Ord a => Tm a -> (NormalizeTm a, Tm a)
normalize' tm@(Var x)
    = NormalizeVar tm # tm
normalize' tm@(Con c)
    = NormalizeCon tm # tm
normalize' tm@(Abs x k e)
    = let (de', e') = normalize' e
       in NormalizeAbs de' tm # Abs x k e'
normalize' tm@(App e1 e2)
    = let (de1', e1') = normalize' e1
          (de2', e2') = normalize' e2
       in case reduce (App e1' e2') of
            Nothing -> NormalizeApp1 de1' de2' tm # App e1' e2'
            Just ({-de', -}e') ->
                let (de'', e'') = normalize' e'
                in NormalizeApp2 de1' de2' de'' tm # e''
normalize' tm@(Union e1 e2)
    = let (de1', e1') = normalize' e1
          (de2', e2') = normalize' e2
       in case reduce (Union e1' e2') of
            Nothing -> NormalizeUnion1 de1' de2' tm # Union e1' e2'
            Just ({-de', -}e') ->
                let (de'', e'') = normalize' e'
                in NormalizeUnion2 de1' de2' de'' tm # e''
normalize' tm@Empty
    = NormalizeEmpty tm # Empty
    
normalize :: Ord a => Tm a -> Tm a
normalize = snd . normalize'

-- | η-expansion

-- TODO: we also need to do "∅-expansion" (or better: generate correct terms in
--       the solver), but we cannot always do this without knowing its sort;
--       instead there currently is a small hack in reduce

etaExpand :: Env -> Tm a -> Fresh (Tm a)
etaExpand env (Var x)
    = do etaExpand' x (lookup' ("etaExpand") x env)
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
