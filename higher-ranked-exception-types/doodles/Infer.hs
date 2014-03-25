module Main where

-- TODO: reconstruct derivation tree

import           Common
import qualified LambdaUnion as LU
import qualified Completion  as C

import Data.Maybe
import Data.Set

-- | Expressions

data Expr
    = Var Name
    | Abs Name Ty Expr
    | App Expr Expr
    
instance Show Expr where
    show (Var   x    ) = "x" ++ show x
    show (Abs   x t e) = "(λx" ++ show x ++ ":" ++ show t ++ "." ++ show e ++ ")"
    show (App   e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    
-- | Exception type reconstruction

type Env = [(Name, ExnTy)]

data Constr
    = Name :< Name
    deriving Show

reconstruct :: Env -> Expr -> Fresh (ExnTy, [Constr])
reconstruct env (Var x)
    = do return (fromJust (lookup x env), [])
reconstruct env (Abs x t e)
    = do undefined
reconstruct env (App e1 e2)
    = do (t1, c1) <- reconstruct env e1
         (t2, c2) <- reconstruct env e2
         (ExnArr t2' t' exn) <- instantiate t1
         error "unfinished"
         

-- * Merge

type KindEnv = [(Name, Kind)]

merge :: KindEnv -> ExnTy -> ExnTy -> [(Name, Exn)]
merge env = undefined
         
-- * Instantiation

substExn :: Name -> Name -> Exn -> Exn
substExn e e' (ExnVar e'')
    | e == e''  = ExnVar e'
    | otherwise = ExnVar e''
substExn e e' (ExnApp exn1 exn2)
    = ExnApp (substExn e e' exn1) (substExn e e' exn2)

substExnTy :: Name -> Name -> ExnTy -> ExnTy
substExnTy e e' (ExnForall e'' k t)
    | e == e''  = ExnForall e'' k t
    | otherwise = ExnForall e'' k (substExnTy e e' t)
substExnTy e e' (ExnBool exn)
    = ExnBool (substExn e e' exn)
substExnTy e e' (ExnList t exn)
    = ExnList (substExnTy e e' t) (substExn e e' exn)
substExnTy e e' (ExnArr t1 t2 exn)
    = ExnArr (substExnTy e e' t1) (substExnTy e e' t2) (substExn e e' exn)
         
instantiate :: ExnTy -> Fresh ExnTy
instantiate (ExnForall e k t)
    = do e' <- fresh
         t' <- instantiate t
         return (substExnTy e e' t')
instantiate t
    = do return t
