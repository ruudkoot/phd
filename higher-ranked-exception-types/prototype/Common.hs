{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns      #-}

module Common where

-- FIXME: make all functions total (and remove dead errors)

import           Names
import qualified LambdaUnion as LU
import           Latex

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
    
instance Show Expr where
    show (Var x     ) = "x" ++ show x
    show (Abs x t e ) = "(λx" ++ show x ++ ":" ++ show t ++ "." ++ show e ++ ")"
    show (App e1 e2 ) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Con True  ) = "true"
    show (Con False ) = "false"
    show (Crash l t ) = "(⚡" ++ l ++ ":" ++ show t ++ ")"
    show (Seq e1 e2 ) = "(" ++ show e1 ++ " seq " ++ show e2 ++ ")"
    show (Fix e     ) = "(fix " ++ show e ++ ")"
    show (Nil t     ) = "(ε:" ++ show t ++ ")"
    show (Cons e1 e2) = "(" ++ show e1 ++ "⸪" ++ show e2 ++ ")"
    show (Case e1 e2 x1 x2 e3)
        = "(case " ++ show e1 ++ " of { ε ↦ " ++ show e2 ++ "; x"
                        ++ show x1 ++ "⸪x" ++ show x2 ++ " ↦ " ++ show e3 ++ "})"
                        
instance Latex Expr where
    latex (Var x     ) = "x_{" ++ show x ++ "}"
    latex (Abs x t e ) = "(\\lambda x_{" ++ show x ++ "}:" ++ latex t ++ "." ++ latex e ++ ")"
    latex (App e1 e2 ) = "(" ++ latex e1 ++ " " ++ latex e2 ++ ")"
    latex (Con True  ) = "true"
    latex (Con False ) = "false"
    latex (Crash l t ) = "(⚡" ++ l ++ ":" ++ latex t ++ ")"
    latex (Seq e1 e2 ) = "(" ++ latex e1 ++ " seq " ++ latex e2 ++ ")"
    latex (Fix e     ) = "(fix " ++ latex e ++ ")"
    latex (Nil t     ) = "(ε:" ++ latex t ++ ")"
    latex (Cons e1 e2) = "(" ++ latex e1 ++ "::" ++ latex e2 ++ ")"
    latex (Case e1 e2 x1 x2 e3)
        = "(case " ++ latex e1 ++ " of { \\epsilon \\mapsto " ++ latex e2 ++ "; x_{"
                        ++ show x1 ++ "}::x_{" ++ show x2 ++ "} \\mapsto " ++ latex e3 ++ "})"

    lhs2tex (Var x     )
        = "Var " ++ show x
    lhs2tex (Abs x t e )
        = "LAMBDA (x_" ++ show x ++ ") (" ++ lhs2tex t ++ ") (" ++ lhs2tex e ++ ")"
    lhs2tex (App e1 e2 )
        = "(" ++ lhs2tex e1 ++ " " ++ lhs2tex e2 ++ ")"
    lhs2tex (Con True  )
        = "True"
    lhs2tex (Con False )
        = "False"
    lhs2tex (Crash l t )
        = "Bottom (" ++ l ++ ") (" ++ lhs2tex t ++ ")"
    lhs2tex (Seq e1 e2 )
        = "Seq (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ ")"
    lhs2tex (Fix e     )
        = "Fix (" ++ lhs2tex e ++ ")"
    lhs2tex (Nil t     )
        = "Nil (" ++ lhs2tex t ++ ")"
    lhs2tex (Cons e1 e2)
        = "Cons (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ ")"
    lhs2tex (Case e1 e2 x1 x2 e3)
        = "Case (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ ") (x_"
            ++ show x1 ++ ") (x_" ++ show x2 ++ ") (" ++ lhs2tex e3 ++ ")"

-- | Types

data Ty
    = Bool
    | Ty :-> Ty
    | List Ty
    deriving Show
    
instance Latex Ty where
    latex Bool        = "bool"
    latex (t1 :-> t2) = "(" ++ latex t1 ++ " \\to " ++ latex t2 ++ ")"
    latex (List t)    = "\\left[" ++ latex t ++ "\\right]"
    
    lhs2tex Bool        = "Bool"
    lhs2tex (t1 :-> t2) = "(" ++ lhs2tex t1 ++ " -> " ++ lhs2tex t2 ++ ")"
    lhs2tex (List t)    = "[" ++ lhs2tex t ++ "]"

data Kind = EXN | Kind :=> Kind
    deriving (Eq, Show)
    
instance Latex Kind where
    latex EXN         = "EXN"
    latex (k1 :=> k2) = latex k1 ++ " \\Rightarrow " ++ latex k2
    
    lhs2tex EXN         = "EXN"
    lhs2tex (k1 :=> k2) = "KindArr (" ++ lhs2tex k1 ++ ") (" ++ lhs2tex k2 ++ ")"

type KindEnv = [(Name, Kind)]

instance Latex (Name, Kind) where
    lhs2tex (show -> e, lhs2tex -> k)
        = "e_" ++ e ++ " : " ++ k

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

instance Show Exn where
    show (ExnEmpty)       = "∅"
    show (ExnUnion e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    show (ExnCon lbl)     = "{" ++ lbl ++ "}"
    show (ExnVar n)       = "e" ++ show n
    show (ExnApp e1 e2)   = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (ExnAbs n k e)   = "(λe" ++ show n ++ ":" ++ show k ++ "." ++ show e ++ ")"
    
instance Latex Exn where
    latex (ExnEmpty)       = "\\emptyset"
    latex (ExnUnion e1 e2) = "(" ++ latex e1 ++ " \\cup " ++ latex e2 ++ ")"
    latex (ExnCon lbl)     = "\\{" ++ lbl ++ "\\}"
    latex (ExnVar n)       = "e_{" ++ show n ++ "}"
    latex (ExnApp e1 e2)   = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (ExnAbs n k e)   = "(\\lambda e_{" ++ show n ++ "}:" ++ latex k ++ "." ++ latex e ++ ")"
    
    lhs2tex (ExnEmpty)       = "ExnEmpty"
    lhs2tex (ExnUnion e1 e2) = "ExnUnion (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ ")"
    lhs2tex (ExnCon lbl)     = "ExnCon (" ++ show lbl ++ ")"
    lhs2tex (ExnVar n)       = "ExnVar (" ++ show n ++ ")"
    lhs2tex (ExnApp e1 e2)   = "ExnApp (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ ")"
    lhs2tex (ExnAbs n k e)   = "ExnAbs (" ++ show n ++ ") (" ++ lhs2tex k ++ ") (" ++ lhs2tex e ++ ")"

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

instance Latex ExnTy where
    latex (ExnForall e k t)
        = "(\\forall e_{" ++ show e ++ "}::" ++ latex k ++ "." ++ latex t ++ ")"
    latex (ExnBool)
        = "bool"
    latex (ExnList t exn)
        = "[" ++ latex t ++ "{" ++ latex exn ++ "}]"
    -- TODO: print top-level annotation on the arrow for readability
    latex (ExnArr t1 exn1 t2 exn2)
        = "(" ++ latex t1 ++ "{" ++ latex exn1 ++ "} \\to "
              ++ latex t2 ++ "{" ++ latex exn2 ++ "})"

    lhs2tex (ExnForall e k t)
        = "ExnForall (" ++ show e ++ ") (" ++ lhs2tex k ++ ") (" ++ lhs2tex t ++ ")"
    lhs2tex (ExnBool)
        = "ExnBool"
    lhs2tex (ExnList t exn)
        = "ExnList (" ++ lhs2tex t ++ ") (" ++ lhs2tex exn ++ ")"
    -- TODO: print top-level annotation on the arrow for readability
    lhs2tex (ExnArr t1 exn1 t2 exn2)
        = "ExnArr (" ++ lhs2tex t1 ++ ") (" ++ lhs2tex exn1 ++ ") ("
              ++ lhs2tex t2 ++ ") (" ++ lhs2tex exn2 ++ ")"


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
