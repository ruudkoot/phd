module Common where

-- TODO: put annotations back on type constructor arguments?

import           Names
import qualified LambdaUnion as LU

import Data.List (delete)

-- | Types

data Ty
    = Bool
    | Ty :-> Ty
    | List Ty
    deriving Show

data Kind = EXN | Kind :=> Kind
    deriving (Eq, Show)

type KindEnv = [(Name, Kind)]
    
kind2sort :: Kind -> LU.Sort
kind2sort EXN         = LU.C
kind2sort (k1 :=> k2) = kind2sort k1 LU.:=> kind2sort k2

sort2kind :: LU.Sort -> Kind
sort2kind LU.C           = EXN
sort2kind (s1 LU.:=> s2) = sort2kind s1 :=> sort2kind s2

-- TODO: replace this with module LambdaUnion
data Exn
    = ExnEmpty
    | ExnUnion Exn Exn
    -- TODO: ExnCon
    | ExnVar Name
    | ExnApp Exn Exn
    | ExnAbs Name Kind Exn

exn2lu :: Exn -> LU.Tm
exn2lu (ExnEmpty      ) = LU.Empty
exn2lu (ExnUnion e1 e2) = LU.Union (exn2lu e1) (exn2lu e2)
exn2lu (ExnVar   n    ) = LU.Var n
exn2lu (ExnApp   e1 e2) = LU.App (exn2lu e1) (exn2lu e2)
exn2lu (ExnAbs   n k e) = LU.Abs n (kind2sort k) (exn2lu e)

lu2exn :: LU.Tm -> Exn
lu2exn (LU.Empty      ) = ExnEmpty
lu2exn (LU.Union e1 e2) = ExnUnion (lu2exn e1) (lu2exn e2)
lu2exn (LU.Var   n    ) = ExnVar n
lu2exn (LU.App   e1 e2) = ExnApp (lu2exn e1) (lu2exn e2)
lu2exn (LU.Abs   n s e) = ExnAbs n (sort2kind s) (lu2exn e)

exnEq :: KindEnv -> Exn -> Exn -> Bool
exnEq env e1 e2
    = LU.semanticallyEqual (map (\(x,k) -> (x, kind2sort k)) env) (exn2lu e1) (exn2lu e2)
    
exnNormalize :: Exn -> Exn
exnNormalize = lu2exn . LU.normalize . exn2lu

instance Show Exn where
    show (ExnEmpty)       = "∅"
    show (ExnUnion e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    show (ExnVar n)       = "e" ++ show n
    show (ExnApp e1 e2)   = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (ExnAbs n k e)   = "(λe" ++ show n ++ ":" ++ show k ++ "." ++ show e ++ ")"

data ExnTy
    = ExnForall Name Kind ExnTy
    | ExnBool
    | ExnList ExnTy Exn
    | ExnArr  ExnTy Exn ExnTy Exn
    
exnTyEq :: KindEnv -> ExnTy -> ExnTy -> Bool
exnTyEq env (ExnForall e k t) (ExnForall e' k' t')
    = k == k' && exnTyEq env t (substExnTy e' e t')
exnTyEq env ExnBool ExnBool
    = True
exnTyEq env (ExnList t exn) (ExnList t' exn')
    = exnTyEq env t t' && exnEq env exn exn'
exnTyEq env (ExnArr t1 exn1 t2 exn2) (ExnArr t1' exn1' t2' exn2')
    = exnTyEq env t1 t1' && exnEq env exn1 exn1'
        && exnTyEq env t2 t2' && exnEq env exn2 exn2'
exnTyEq env _ _
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
