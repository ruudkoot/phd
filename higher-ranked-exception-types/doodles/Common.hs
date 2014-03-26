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
    | ExnBool
    | ExnList ExnTy Exn
    | ExnArr  ExnTy Exn ExnTy Exn

instance Show ExnTy where
    show (ExnForall e k t)
        = "(∀e" ++ show e ++ "::" ++ show k ++ "." ++ show t ++ ")"
    show (ExnBool)
        = "bool"
    show (ExnList t exn)
        = "[" ++ show t ++ "{" ++ show exn ++ "}]"
    -- TODO: print top-level annotation on the arrow for readability
    show (ExnArr t1 exn1 t2 exn2)
        = "(" ++ show t1 ++ "{" ++ show exn1 ++ "} -> "
              ++ show t2 ++ "{" ++ show exn2 ++ "})"

data Kind = EXN | Kind :=> Kind
    deriving Show
