module Main where

-- TODO: reconstruct derivation tree

import           Common
import qualified LambdaUnion as LU
import qualified Completion  as C

-- | Expressions

data Expr
    = Var Name
    | Abs Name Ty Expr
    | App Expr Expr
    
instance Show Expr where
    show (Var x    ) = "x" ++ show x
    show (Abs x t e) = "(λx" ++ show x ++ ":" ++ show t ++ "." ++ show e ++ ")"
    show (App e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    
-- | Exception type reconstruction

type Env = [(Name, (ExnTy, Exn))]

data Constr = Exn :<: Name
    deriving Show

reconstruct :: Env -> Expr -> Fresh (ExnTy, Name, [Constr])
reconstruct env (Var x)
    = do let Just (t, exn) = lookup x env
         e <- fresh
         return (t, e, [exn :<: e])
reconstruct env (Abs x ty tm)
    = do (t1', exn1, env1) <- C.complete [] ty
         exn <- fresh
         let env' = (x, (t1', ExnVar exn)) : env
         (t2', exn2, c1) <- reconstruct env' tm
         let v = [exn] ++ map fst env1 ++ fev env
         let exn2' = solve c1 v exn2
         let t' = ExnForall exn EXN (C.forallFromEnv env1 (
                    ExnArr t1' (ExnVar exn) t2' exn2'
                ))
         e <- fresh
         return (t', e, [])
reconstruct env (App e1 e2)
    = do (t1, exn1, c1) <- reconstruct env e1
         (t2, exn2, c2) <- reconstruct env e2
         (ExnArr t2' (ExnVar exn2') t' exn') <- instantiate t1
         let subst = [(exn2', ExnVar exn2)] <.> merge [] t2 t2'
         e <- fresh
         let c = c1 ++ c2 ++ [substExn' subst exn' :<: e, ExnVar exn1 :<: e]
         return (substExnTy' subst  t', e, c)

fev :: Env -> [Name]
fev = error "fev"

solve :: [Constr] -> [Name] -> Name -> Exn
solve = error "solve"

type Subst = [(Name, Exn)]

-- TODO: check domains are non-intersecting
(<.>) :: Subst -> Subst -> Subst
subst1 <.> subst2 = subst1 ++ map (\(x,exn) -> (x, substExn' subst1 exn)) subst2

substExn' :: Subst -> Exn -> Exn
substExn' = error "substExn'"

substExnTy' :: Subst -> ExnTy -> ExnTy
substExnTy' = error "substExnTy'"
         
-- * Merge

type KindEnv = [(Name, Kind)]

merge :: KindEnv -> ExnTy -> ExnTy -> Subst
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
substExnTy e e' (ExnBool)
    = ExnBool
substExnTy e e' (ExnList t exn)
    = ExnList (substExnTy e e' t) (substExn e e' exn)
substExnTy e e' (ExnArr t1 exn1 t2 exn2)
    = ExnArr (substExnTy e e' t1) (substExn e e' exn1)
             (substExnTy e e' t2) (substExn e e' exn2)
         
instantiate :: ExnTy -> Fresh ExnTy
instantiate (ExnForall e k t)
    = do e' <- fresh
         t' <- instantiate t
         return (substExnTy e e' t')
instantiate t
    = do return t
