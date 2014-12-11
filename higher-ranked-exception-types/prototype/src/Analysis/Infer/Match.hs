module Analysis.Infer.Match (
    match
) where

import Control.Monad (replicateM, when)

import Analysis.Names
import Analysis.Common

-- | Match (merge, meet)

-- FIXME: failure to use fresh names for the binder did not cause the problem!

match :: KindEnv -> ExnTy -> ExnTy -> Fresh Subst
match env (ExnBool) (ExnBool)
    = return []
match env (ExnForall e k t) (ExnForall e' k' t')
    | k == k'   = match ((e,k) : env) t (substExnTy e' e t')
    | otherwise = error "match: kind mismatch"
-- FIXME: correct definition for lists?
match env (ExnList t exn) (ExnList t' exn')
    = do when (not (null env)) $ error $ {- ASSERT -}
            "match: list; t = " ++ show t ++"; t' = " ++ show t' ++
            "; env = " ++ show env
         let (e, es) = deapply exn'
         when (not (null es)) $ error $ {- ASSERT -}
            "match: list; t = " ++ show t ++"; t' = " ++ show t' ++
            "; env = " ++ show env ++ "; e = " ++ show e ++ "; es = " ++ show es
         -- FIXME: REFRESH!!!
         subst <- match env t t'
         return $ [(e, reapply env es (repeat $ error "match: list") exn)] <.> subst
match env t@(ExnArr t1 (ExnVar exn1) t2 exn2) t'@(ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq env t1 t1', exn1 == exn1'
        = do let (e, es) = deapply exn2'
             fs <- replicateM (length es) fresh
             subst <- match env t2 t2'
             return $ [(e, reapply env es fs exn2)] <.> subst
    | otherwise = error $ "match: function space (t = "   ++ show t ++
                          "; t' = "  ++ show t' ++ "; env = " ++ show env
match env t t'
    = error $ "match: t = " ++ show t ++ "; t' = " ++ show t' ++ "; env = " ++ show env

-- | Split and recombine an applied fuction into a function and its arguments

-- NOTE: here the fully-appliedness and left-to-rightness comes into play
-- TODO: check this restriction in never violated
-- TODO: encode this restriction into Exn?
deapply :: Exn -> (Name, [Name])
deapply (ExnVar e) = (e, [])
deapply (ExnApp e1 (ExnVar e2))
    = let (e, es) = deapply e1
       in (e, es ++ [e2])           -- TODO: keep this in reverse order?
deapply _ = error "deapply: malformed"

reapply :: KindEnv -> [Name] -> [Name] -> Exn -> Exn
reapply env es fs exn
    = foldr (\(e,f) r -> ExnAbs f (lookup' "reapply" e env) r)
            (substExn' (zip es (map ExnVar fs)) exn)
            (zip es fs)
