module Analysis.Infer.Match (
    match
) where

import Analysis.Names
import Analysis.Common

-- | Match (merge, meet)

match :: KindEnv -> ExnTy -> ExnTy -> Subst
match env (ExnBool) (ExnBool)
    = []
match env (ExnForall e k t) (ExnForall e' k' t')
    | k == k'   = match ((e,k) : env) t (substExnTy e' e t')
    | otherwise = error "match: kind mismatch"
-- FIXME: correct definition for lists?
match env (ExnList t exn) (ExnList t' exn')
    = let (e, es) = deapply exn'
       in [(e, reapply env es exn)] <.> match env t t'
match env t@(ExnArr t1 (ExnVar exn1) t2 exn2) t'@(ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq env t1 t1', exn1 == exn1'
        = let (e, es) = deapply exn2'
           in [(e, reapply env es exn2)] <.> match env t2 t2'
    | otherwise = error $ "match: function space (t = "   ++ show t
                          ++ "; t' = "  ++ show t' ++ "; env = " ++ show env
match env t t'
    = error $ "match: t = " ++ show t ++ "; t' = " ++ show t' ++ "; env = " ++ show env
    
-- NOTE: here the fully-appliedness and left-to-rightness comes into play
-- TODO: check this restriction in never violated
-- TODO: encode this restriction into Exn?
deapply :: Exn -> (Name, [Name])
deapply (ExnVar e) = (e, [])
deapply (ExnApp e1 (ExnVar e2))
    = let (e, es) = deapply e1
       in (e, es ++ [e2])           -- TODO: keep this in reverse order?
deapply _ = error "deapply: malformed"

reapply :: KindEnv -> [Name] -> Exn -> Exn
reapply env es exn
    = foldr (\e r -> ExnAbs e (lookup' "reapply" e env) r) exn es
