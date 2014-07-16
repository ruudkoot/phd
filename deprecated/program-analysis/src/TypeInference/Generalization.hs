module TypeInference.Generalization
    (gen)
where

import Data.Set

import Language.Haskell.Exts.Annotated

import Common
import Refinement

import TCMonad

import Solver.Unification

-- | Generalization

-- NOTE: Assumes tau is a type and not a type scheme (should be fine without
--       higher-ranked types.)
-- NOTE: Does not explicitly quantify over unsolved constraints (i.e., all
--       annotation variables appearing in constraints, but not mentioned in the
--       quantifier are implicitly existentially quantified.)
--       FIXME: We probably should (annotations not bound in the environment...)
-- NOTE: Currently does not rely on being in the TC monad (but perhaps a solver
--       would like to generate fresh names?)

gen :: Env -> Type Phi -> [Constr] -> [RefConstr] -> TC (Type Phi, [Constr])

gen gamma tau cs rcs
    = do let subst  = unify cs
         let tau'   = subst `applySubst` tau
         let rcs'   = subst `applySubst` rcs
         let alphas = ftv tau' \\ ftvEnv gamma
         let betas  = fav tau' \\ favEnv gamma
         let sigma  = TyForall (UC { uc = rcs' }) (Just (fmap (UnkindedVar NoPhi) (toList alphas ++ toList betas))) Nothing tau'
         return (sigma, subst)
