module Analysis.LambdaUnion.Equality where

import Analysis.LambdaUnion.Syntax
import Analysis.LambdaUnion.Reduce
import Analysis.LambdaUnion.ReduceNew

import Control.Monad.State

-- | Syntactic equality up to alpha-renaming

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


-- | Semantic equality

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
     
     
-- ReduceNew version
semanticallyEqual' :: (Ord a, Show a) => Env -> Tm a -> Tm a -> Bool
semanticallyEqual' env e1 e2 =
    let e1' = fst . fst $ runState (toTm' env e1) (maxName e1 + 1001)
        e2' = fst . fst $ runState (toTm' env e2) (maxName e2 + 1001)
     in synEqAlpha ((fromTm' . normalize') e1') ((fromTm' . normalize') e2')
