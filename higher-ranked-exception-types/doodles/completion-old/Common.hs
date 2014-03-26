module Common where

-- TODO: put annotations back on type constructor arguments?

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
    
evalFresh = evalState

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
    show (ExnVar n)     = "e" ++ show n
    show (ExnApp e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"

data ExnTy
    = ExnForall Name Kind ExnTy
    | ExnBool             Exn
    | ExnList ExnTy       Exn
    | ExnArr  ExnTy ExnTy Exn

instance Show ExnTy where
    show (ExnForall e k t)
        = "(∀e" ++ show e ++ "::" ++ show k ++ "." ++ show t ++ ")"
    show (ExnBool exn)
        = "bool{" ++ show exn ++ "}"
    show (ExnList t exn)
        = "[" ++ show t ++ "]{" ++ show exn ++ "}"
    show (ExnArr t1 t2 exn)
        = "(" ++ show t1 ++ " --{" ++ show exn ++ "}-> " ++ show t2 ++ ")"

data Kind = EXN | Kind :=> Kind
    deriving Show
