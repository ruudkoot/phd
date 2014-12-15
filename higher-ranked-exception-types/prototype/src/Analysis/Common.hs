{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Common where

-- FIXME: make all functions total (and remove dead errors)

import           Analysis.Names
import qualified Analysis.LambdaUnion as LU
import           Analysis.Print

import Data.List (delete)

-- | Logging

type Log = [String]

-- | Expressions

-- FIXME: move to Common (or Ty to here?)

data Expr
    = Var Name
    | Abs Name Ty Expr
    | App Expr Expr
    | Con Bool
    | Crash Lbl Ty
    | Seq Expr Expr
    | Fix Expr
    | Nil Ty
    | Cons Expr Expr
    | Case Expr Expr Name Name Expr
    deriving (Read, Show)
    
instance Latex Expr where
    latex (Var x     ) = "x_{" ++ show x ++ "}"
    latex (Abs x t e ) = "(\\lambda x_{" ++ show x ++ "}:" ++ latex t ++ "." ++ latex e ++ ")"
    latex (App e1 e2 ) = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (Con True  ) = "\\mathbf{true}"
    latex (Con False ) = "\\mathbf{false}"
    latex (Crash l t ) = "(⚡" ++ l ++ ":" ++ latex t ++ ")"
    latex (Seq e1 e2 ) = "(" ++ latex e1 ++ " \\mathbf{seq} " ++ latex e2 ++ ")"
    latex (Fix e     ) = "(\\mathbf{fix}\\ " ++ latex e ++ ")"
    latex (Nil t     ) = "(\\epsilon:" ++ latex t ++ ")"
    latex (Cons e1 e2) = "(" ++ latex e1 ++ " :: " ++ latex e2 ++ ")"
    latex (Case e1 e2 x1 x2 e3)
        = "(\\mathbf{case}\\ " ++ latex e1 ++ "\\ \\mathbf{of}\\ \\{ ε \\mapsto "
            ++ latex e2 ++ "; x_{" ++ show x1 ++ "}::x_{" ++ show x2 ++ "} \\mapsto "
            ++ latex e3 ++ "\\})"

-- | Types

data Ty
    = Bool
    | Ty :-> Ty
    | List Ty
    deriving (Read, Show)
    
instance Latex Ty where
    latex Bool
        = "\\textbf{bool}"
    latex (t1 :-> t2) 
        = "\\left(" ++ latex t1 ++ " \\rightarrow " ++ latex t2 ++ "\\right)"
    latex (List t)
        = "\\left[" ++ latex t ++ "\\right]"

data Kind = EXN | Kind :=> Kind
    deriving (Eq, Read, Show)
    
instance Latex Kind where
    latex EXN         = "E"
    latex (k1 :=> k2) = "(" ++ latex k1 ++ " \\Rightarrow " ++ latex k2 ++ ")"

type KindEnv = [(Name, Kind)]

instance Latex (Name, Kind) where
    latex (show -> e, latex -> k)
        = "e_{" ++ e ++ "} : " ++ k

kind2sort :: Kind -> LU.Sort
kind2sort EXN         = LU.C
kind2sort (k1 :=> k2) = kind2sort k1 LU.:=> kind2sort k2

sort2kind :: LU.Sort -> Kind
sort2kind LU.C           = EXN
sort2kind (s1 LU.:=> s2) = sort2kind s1 :=> sort2kind s2

type Lbl = String

-- TODO: replace this with module LambdaUnion
data Exn
    = ExnEmpty
    | ExnUnion Exn Exn
    | ExnCon Lbl
    | ExnVar Name
    | ExnApp Exn Exn
    | ExnAbs Name Kind Exn
    deriving (Read, Show)

exn2lu :: Exn -> LU.Tm Lbl
exn2lu (ExnEmpty      ) = LU.Empty
exn2lu (ExnUnion e1 e2) = LU.Union (exn2lu e1) (exn2lu e2)
exn2lu (ExnCon   lbl  ) = LU.Con lbl
exn2lu (ExnVar   n    ) = LU.Var n
exn2lu (ExnApp   e1 e2) = LU.App (exn2lu e1) (exn2lu e2)
exn2lu (ExnAbs   n k e) = LU.Abs n (kind2sort k) (exn2lu e)

lu2exn :: LU.Tm Lbl -> Exn
lu2exn (LU.Empty      ) = ExnEmpty
lu2exn (LU.Con   lbl  ) = ExnCon lbl
lu2exn (LU.Union e1 e2) = ExnUnion (lu2exn e1) (lu2exn e2)
lu2exn (LU.Var   n    ) = ExnVar n
lu2exn (LU.App   e1 e2) = ExnApp (lu2exn e1) (lu2exn e2)
lu2exn (LU.Abs   n s e) = ExnAbs n (sort2kind s) (lu2exn e)

exnEq :: KindEnv -> Exn -> Exn -> Bool
exnEq env e1 e2
    = LU.semanticallyEqual (map (\(x,k) -> (x, kind2sort k)) env) (exn2lu e1) (exn2lu e2)

exnNormalize :: Exn -> Exn
exnNormalize = lu2exn . LU.normalize . exn2lu

instance Latex Exn where
    latex (ExnEmpty)       = "\\emptyset"
    latex (ExnUnion e1 e2) = "(" ++ latex e1 ++ "\\cup " ++ latex e2 ++ ")"
    latex (ExnCon lbl)     = "{" ++ lbl ++ "}"
    latex (ExnVar n)       = "e_{" ++ show n ++ "}"
    latex (ExnApp e1 e2)   = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (ExnAbs n k e)   = "(\\lambda e_{" ++ show n ++ "}:" ++ latex k ++ "." ++ latex e ++ ")"
    
data ExnTy
    = ExnForall Name Kind ExnTy
    | ExnBool
    | ExnList ExnTy Exn
    | ExnArr  ExnTy Exn ExnTy Exn
    deriving (Read, Show)

checkExnTy :: KindEnv -> ExnTy -> Bool    -- FIXME: also check kind-correctness!
checkExnTy env (ExnForall e k t)
    | Just _ <- lookup e env = False
    | otherwise = checkExnTy ((e,k):env) t
checkExnTy env ExnBool
    = True
checkExnTy env (ExnList t exn)
    = checkExnTy env t && checkExn env exn
checkExnTy env (ExnArr t1 exn1 t2 exn2)
    = checkExnTy env t1 && checkExnTy env t2
        && checkExn env exn1 && checkExn env exn2
        
checkExn :: KindEnv -> Exn -> Bool        -- FIXME: also check kind-correctness!
checkExn env (ExnEmpty)
    = True
checkExn env (ExnUnion exn1 exn2)
    = checkExn env exn1 && checkExn env exn2
checkExn env (ExnCon lbl)
    = True
checkExn env (ExnVar x)
    | Just _ <- lookup x env = True
    | otherwise              = False
checkExn env (ExnApp exn1 exn2)
    = checkExn env exn1 && checkExn env exn2
checkExn env (ExnAbs e k exn)
    | Just _ <- lookup e env = False
    | otherwise              = checkExn ((e,k):env) exn

exnTyEq :: KindEnv -> ExnTy -> ExnTy -> Bool
exnTyEq env (ExnForall e k t) (ExnForall e' k' t')
    = k == k' && exnTyEq ((e,k) : env) t (substExnTy e' e t')
exnTyEq env ExnBool ExnBool
    = True
exnTyEq env (ExnList t exn) (ExnList t' exn')
    = exnTyEq env t t' && exnEq env exn exn'
exnTyEq env (ExnArr t1 exn1 t2 exn2) (ExnArr t1' exn1' t2' exn2')
    = exnTyEq env t1 t1' && exnEq env exn1 exn1'
        && exnTyEq env t2 t2' && exnEq env exn2 exn2'
exnTyEq env _ _
    = False

instance Latex ExnTy where
    latex (ExnForall e k t)
        = "\\left(\\forall e_{" ++ show e ++ "}::" ++ latex k ++ "." ++ latex t ++ "\\right)"
    latex (ExnBool)
        = "\\mathbf{bool}"
    latex (ExnList t exn)
        = "\\left[" ++ latex t ++ "\\{" ++ latex exn ++ "\\}\\right]"
    -- TODO: print top-level annotation on the arrow for readability
    latex (ExnArr t1 exn1 t2 exn2)
        = "\\left(" ++ latex t1 ++ "\\{" ++ latex exn1 ++ "\\} \\rightarrow "
              ++ latex t2 ++ "\\{" ++ latex exn2 ++ "\\}\\right)"

-- | Free exception variables

fevExn :: Exn -> [Name]
fevExn (ExnVar e)     = [e]
fevExn (ExnCon c)     = []
fevExn (ExnApp e1 e2) = fevExn e1 ++ fevExn e2
fevExn (ExnAbs n k e) = delete n (fevExn e)

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
substExn e e' (ExnAbs n k e'')
    | e == n    = ExnAbs n k e''
    | otherwise = ExnAbs n k (substExn e e' e'')
substExn e e' (ExnApp exn1 exn2)
    = ExnApp (substExn e e' exn1) (substExn e e' exn2)
substExn e e' ExnEmpty
    = ExnEmpty
substExn e e' (ExnUnion exn1 exn2)
    = ExnUnion (substExn e e' exn1) (substExn e e' exn2)
substExn e e' (ExnCon c)
    = ExnCon c
substExn e e' e''
    = error $ "substExn: e'' = " ++ show e''
                    ++ "; e = " ++ show e ++ "; e' = " ++ show e'

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
substExn' subst exn@(ExnVar x)
    | Just exn' <- lookup x subst = exn'
    | otherwise                   = exn
substExn' subst (ExnAbs x k e)
    = ExnAbs x k (substExn' (deleteKey x subst) e)
substExn' subst (ExnApp e1 e2)
    = ExnApp (substExn' subst e1) (substExn' subst e2)
substExn' subst ExnEmpty
    = ExnEmpty
substExn' subst (ExnUnion e1 e2)
    = ExnUnion (substExn' subst e1) (substExn' subst e2)
substExn' subst e
    = error $ "substExn': e = " ++ show e ++ "; subst = " ++ show subst

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
