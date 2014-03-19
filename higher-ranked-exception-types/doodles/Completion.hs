{-# LANGUAGE ViewPatterns #-}

-- TODO: use right-to-left syntax for environments to avoid headaches.
-- TODO: rename env_i, env_j, ... to env0, env1, ...
-- TODO: do we get nicer types if we generate fresh name later?

module Main where

import Control.Monad
import Control.Monad.State

-- | Names

type Name = Int

type Fresh a = State Name a

fresh :: Fresh Name
fresh = do
    name <- get
    modify (+1)
    return name

-- | Types

data Ty
    = Bool
    | Ty :-> Ty
    | List Ty
    deriving Show

data Exn
    = ExnVar Name
    | ExnApp Exn Exn

instance Show Exn where
    show (ExnVar n) = "e" ++ show n
    show (ExnApp e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"

data ExnTy
    = ExnForall Name Kind ExnTy
    | ExnBool             Exn
    | ExnList ExnTy       Exn
    | ExnArr  ExnTy ExnTy Exn

instance Show ExnTy where
    show (ExnForall e k t) = "(∀e" ++ show e ++ "::" ++ show k ++ "." ++ show t ++ ")"
    show (ExnBool exn) = "bool{" ++ show exn ++ "}"
    show (ExnList t exn) = "[" ++ show t ++ "]{" ++ show exn ++ "}"
    show (ExnArr t1 t2 exn) = "(" ++ show t1 ++ " -{" ++ show exn ++ "}-> " ++ show t2 ++ ")"

data Kind = EXN | Kind :=> Kind
    deriving Show

type Env = [(Name, Kind)]

-- | Completion

complete' :: Env -> Ty -> (ExnTy, Env)
complete' env ty = evalState (complete env ty) 0

complete :: Env -> Ty -> Fresh (ExnTy, Env)
complete env_i Bool = do
    e <- fresh
    return ( ExnBool (exnFromEnv (ExnVar e) env_i)
           , [(e, kindFromEnv env_i)]              )
complete env_i (List t) = do
    (t', env_j) <- complete env_i t
    e <- fresh
    return ( ExnList t' (exnFromEnv (ExnVar e) env_i)
           , env_j ++ [(e, kindFromEnv env_i)]        )
complete env_i (t1 :-> t2) = do
    (t1', env_j) <- complete [] t1 -- fully-flexible = in any context
    (t2', env_k) <- complete (env_j ++ env_i) t2
    e <- fresh
    return ( forallFromEnv env_j (ExnArr t1' t2' (exnFromEnv (ExnVar e) env_i))
           , env_k ++ [(e, kindFromEnv env_i)]                        )

exnFromEnv :: Exn -> Env -> Exn
exnFromEnv exn (map fst -> es) = foldr (\e r -> ExnApp r (ExnVar e)) exn es

forallFromEnv :: Env -> ExnTy -> ExnTy
forallFromEnv env exn = foldl (\r (e,k) -> ExnForall e k r) exn env

kindFromEnv :: Env -> Kind
kindFromEnv (map snd -> ks) = foldl (flip (:=>)) EXN ks
