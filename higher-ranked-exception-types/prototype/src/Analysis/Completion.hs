{-# LANGUAGE ViewPatterns #-}

-- TODO: use right-to-left syntax for environments to avoid headaches.
-- TODO: pretty print types
-- NOTE: fresh variable are generated in an order that results in nice types

module Analysis.Completion where

import Analysis.Names
import Analysis.Common

type Env = [(Name, Kind)]

-- | Completion

complete' :: Env -> Ty -> (ExnTy, Exn, Env)
complete' env ty = fst $ runFreshLog (complete env ty) 1

complete :: Env -> Ty -> FreshLog Log (ExnTy, Exn, Env)
complete env0 Bool = do
    e <- fresh
    return (ExnBool
           ,exnFromEnv (ExnVar e) env0
           ,[(e, kindFromEnv env0)])
complete env0 (List t) = do
    e <- fresh
    (t', exn, env1) <- complete env0 t
    return (ExnList t' exn
           ,exnFromEnv (ExnVar e) env0
           ,env1 ++ [(e, kindFromEnv env0)])
complete env0 (t1 :-> t2) = do
    (t1', exn1, env1) <- complete [] t1            -- fully-flexible = in any context
    e <- fresh
    (t2', exn2, env2) <- complete (env1 ++ env0) t2
    return (forallFromEnv env1 (ExnArr t1' exn1 t2' exn2)
           ,exnFromEnv (ExnVar e) env0
           ,env2 ++ [(e, kindFromEnv env0)])

exnFromEnv :: Exn -> Env -> Exn
exnFromEnv exn (map fst -> es) = foldr (\e r -> ExnApp r (ExnVar e)) exn es

forallFromEnv :: Env -> ExnTy -> ExnTy
forallFromEnv env exn = foldl (\r (e,k) -> ExnForall e k r) exn env

kindFromEnv :: Env -> Kind
kindFromEnv (map snd -> ks) = foldl (flip (:=>)) EXN ks
