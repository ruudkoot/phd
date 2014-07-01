module TypeInference.Instantiation
    (inst)
where

import Control.Monad

import Data.Map

import Language.Haskell.Exts.Annotated

import Common
import Refinement

import TCMonad

-- | Instantiation

inst :: Type Phi -> TC (Type Phi, [RefConstr])

inst  (TyForall (UC { uc = cs }) (Just varBinds) Nothing t)
    = do fvs   <- replicateM (length varBinds) freshName
         let sigma = fromList $ zipWith (\(UnkindedVar NoPhi name) f -> (name, f)) varBinds fvs
         return (sigma $@* t, (Subst {annSubst = sigma}) `applySubst` cs)
inst  t
    = return (t, []) --error "inst: not a type scheme"
