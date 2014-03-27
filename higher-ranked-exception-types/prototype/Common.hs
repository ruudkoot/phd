module Common where

-- TODO: put annotations back on type constructor arguments?

import Control.Monad
import Control.Monad.State
import Data.List (delete)

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
    | ExnAbs Name Kind Exn
    
instance Eq Exn where
    ExnVar n == ExnVar n'
        = n == n'
    ExnApp e1 e2 == ExnApp e1' e2'
        = e1 == e1' && e2 == e2'
    ExnAbs n k e == ExnAbs n' k' e'
        = k == k' && e == substExn n' n e'
    _ == _
        = False

instance Show Exn where
    show (ExnVar n)     = "e" ++ show n
    show (ExnApp e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (ExnAbs n k e) = "(λe" ++ show n ++ ":" ++ show k ++ "." ++ show e ++ ")"

data ExnTy
    = ExnForall Name Kind ExnTy
    | ExnBool
    | ExnList ExnTy Exn
    | ExnArr  ExnTy Exn ExnTy Exn
    
instance Eq ExnTy where
    ExnForall e k t == ExnForall e' k' t'
        = k == k' && t == substExnTy e' e t'
    ExnBool == ExnBool
        = True
    ExnList t exn == ExnList t' exn'
        = t == t' && exn == exn'
    ExnArr t1 exn1 t2 exn2 == ExnArr t1' exn1' t2' exn2'
        = t1 == t1' && exn1 == exn1' && t2 == t2' && exn2 == exn2'
    _ == _
        = False

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
    deriving (Eq, Show)
    
-- | Free exception variables

fevExn :: Exn -> [Name]
fevExn (ExnVar e)     = [e]
fevExn (ExnApp e1 e2) = fevExn e1 ++ fevExn e2

fevExnTy :: ExnTy -> [Name]
fevExnTy (ExnForall e k t)
    = delete e (fevExnTy t)
fevExnTy (ExnBool)
    = []
fevExnTy (ExnList t e)
    = fevExnTy t ++ fevExn e
fevExnTy (ExnArr t1 exn1 t2 exn2)
    = fevExnTy t1 ++ fevExn exn1 ++ fevExnTy t2 ++ fevExn exn2

-- | Substitution

type Subst = [(Name, Exn)]

-- TODO: somewhat redundant with substExn'
substExn :: Name -> Name -> Exn -> Exn
substExn e e' (ExnVar e'')
    | e == e''  = ExnVar e'
    | otherwise = ExnVar e''
substExn e e' (ExnApp exn1 exn2)
    = ExnApp (substExn e e' exn1) (substExn e e' exn2)

-- TODO: somewhat redundant with substExnTy'
substExnTy :: Name -> Name -> ExnTy -> ExnTy
substExnTy e e' (ExnForall e'' k t)
    -- FIXME: check for possibility of variable capture
    | e == e''  = ExnForall e'' k t
    | otherwise = ExnForall e'' k (substExnTy e e' t)
substExnTy e e' (ExnBool)
    = ExnBool
substExnTy e e' (ExnList t exn)
    = ExnList (substExnTy e e' t) (substExn e e' exn)
substExnTy e e' (ExnArr t1 exn1 t2 exn2)
    = ExnArr (substExnTy e e' t1) (substExn e e' exn1)
             (substExnTy e e' t2) (substExn e e' exn2)

-- TODO: check domains are non-intersecting
(<.>) :: Subst -> Subst -> Subst
subst1 <.> subst2 = subst1 ++ map (\(x,exn) -> (x, substExn' subst1 exn)) subst2

substExn' :: Subst -> Exn -> Exn
substExn' subst exn@(ExnVar e)
    | Just exn' <- lookup e subst = exn'
    | otherwise                   = exn
substExn' subst (ExnApp e1 e2)
    = ExnApp (substExn' subst e1) (substExn' subst e2)

substExnTy' :: Subst -> ExnTy -> ExnTy
substExnTy' subst (ExnForall e k t)
    -- FIXME: check for possibility of variable capture
    = ExnForall e k (substExnTy' (deleteKey e subst) t)
substExnTy' subst (ExnBool)
    = ExnBool
substExnTy' subst (ExnList t exn)
    = ExnList (substExnTy' subst t) (substExn' subst exn)
substExnTy' subst (ExnArr t1 exn1 t2 exn2)
    = ExnArr (substExnTy' subst t1) (substExn' subst exn1)
             (substExnTy' subst t2) (substExn' subst exn2)

-- | Miscellaneous
    
deleteKey :: Eq a => a -> [(a,b)] -> [(a,b)]
deleteKey k []
    = []
deleteKey k ((x1,x2):xs)
    | k == x1   =           deleteKey k xs
    | otherwise = (x1,x2) : deleteKey k xs
