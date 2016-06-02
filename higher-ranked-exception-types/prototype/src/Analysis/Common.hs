{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Common (
    Expr(..),
    ElabTm(..),
    checkExpr,
    Ty(..),
    Kind(..),
    KindEnv,
    Lbl,
    Exn(..),
    ExnTy(..),
    underlying,
    fevExn,
    fevExnTy,
    checkExnTy,
    exnNormalize,
    exnEq,
    exnTyEq,
    isSubeffect,
    isSubtype,
    simplifyExn,
    simplifyExnTy,
    Subst,
    substExn',
    substExnTy,
    substExnTy',
    (<.>)
) where

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
    | BinOp Expr Expr
    | If Expr Expr Expr
    | Crash Lbl Ty
    | Seq Expr Expr
    | Fix Name Ty Expr
    | Fix_ Expr
    | Nil Ty
    | Cons Expr Expr
    | Case Expr Expr Name Name Expr
    deriving (Read, Show)

data ElabTm
    = Var' Name
    | Con' Bool
    | Crash' Lbl Ty
    | Abs' Name ExnTy Exn ElabTm
    | AnnAbs Name Kind ElabTm
    | App' ElabTm ElabTm
    | AnnApp ElabTm Exn
    | Fix' Name ExnTy Exn ElabTm
    | Fix'_ ElabTm
    | BinOp' ElabTm ElabTm
    | Seq' ElabTm ElabTm
    | If' ElabTm ElabTm ElabTm
    | Nil' Ty
    | Cons' ElabTm ElabTm
    | Case' ElabTm ElabTm Name Name ElabTm
    deriving (Read, Show)

type TyEnv = [(Name, Ty)]

checkExpr :: TyEnv -> Expr -> Maybe Ty
checkExpr env (Var x)
    = lookup x env
checkExpr env (Abs x t e)
    = case lookup x env of
        Nothing -> do t' <- checkExpr ((x,t):env) e
                      return (t :-> t')
        _       -> error "shadowing (Abs)"
checkExpr env (App e1 e2)
    = case checkExpr env e1 of
        Just (t1 :-> t2) -> if checkExpr env e2 == Just t1 then return t2 else Nothing
        _                -> error "type (App)"
checkExpr env (Con _)
    = return Bool
checkExpr env (BinOp e1 e2)
    = case checkExpr env e1 of
        Just Int -> case checkExpr env e2 of
            Just Int -> return Bool
            _        -> error "type (BinOp, e2)"
        _        -> error "type (BinOp, e1)"
checkExpr env tm@(If e1 e2 e3)
    = case checkExpr env e1 of
        Just Bool -> if checkExpr env e2 == checkExpr env e3 then
                         checkExpr env e2
                     else
                         error "type (If, body)"
        _         -> error "type (If, guard)"
checkExpr env (Crash _ t)
    = return t
checkExpr env (Seq e1 e2)
    = do _ <- checkExpr env e1
         checkExpr env e2
checkExpr env (Fix x t e)
    = case lookup x env of
        Nothing -> do t' <- checkExpr ((x,t):env) e
                      if t == t' then return t else error "type (Fix)"
        _       -> error "shadowing (Fix)"
checkExpr env (Fix_ e)
    = case checkExpr env e of
        Just (t1 :-> t2) -> if t1 == t2 then return t1 else error "type (Fix_, type 2)"
        _                -> error $ "type (Fix_, type 1)"
checkExpr env (Nil t)
    = return (List t)
checkExpr env (Cons e1 e2)
    = do t1 <- checkExpr env e1
         case checkExpr env e2 of
            Just (List t2) -> if t1 == t2 then return (List t1) else Nothing
            _              -> error "type (Cons, type)"
checkExpr env (Case e1 e2 x1 x2 e3)
    = do () <- if x1 == x2 then error "non-linearity (Case)" else return ()
         () <- case lookup x1 env of
                 Nothing -> return ()
                 _       -> error "shadowing (Case, 1)"
         () <- case lookup x2 env of
                 Nothing -> return ()
                 _       -> error "shadowing (Case, 2)"
         case checkExpr env e1 of
            Just (List t1) -> do t2 <- checkExpr env e2
                                 t3 <- checkExpr ((x1,t1):(x2,List t1):env) e3
                                 if t2 == t3 then
                                    checkExpr env e2
                                 else
                                    error "type (Case, type 2)"
            _              -> error "type (Case, type 1)"

instance Latex Expr where
    latex (Var x)
        = "x_{" ++ show x ++ "}"
    latex (Abs x t e)  
        = "(\\lambda x_{" ++ show x ++ "}:" ++ latex t ++ "." ++ latex e ++ ")"
    latex (App e1 e2)
        = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (Con True)
        = "\\mathbf{true}"
    latex (Con False)
        = "\\mathbf{false}"
    latex (BinOp e1 e2)
        = "(" ++ latex e1 ++ "\\ \\oplus\\ " ++ latex e2 ++ ")"
    latex (If e1 e2 e3)
        = "(\\mathbf{if}\\ " ++ latex e1 ++ "\\ \\mathbf{then}\\ " ++ latex e2
            ++ "\\ \\mathbf{else}\\ " ++ latex e3 ++ ")"
    latex (Crash l t)  
        = "⚡^{\\mathrm{" ++ l ++ "}}_{" ++ latex t ++ "}"
    latex (Seq e1 e2)
        = "(" ++ latex e1 ++ "\\ \\mathbf{seq}\\ " ++ latex e2 ++ ")"
    latex (Fix x t e)
        = "(\\mathbf{fix}\\ x_{" ++ show x ++ "}:" ++ latex t ++ "." ++ latex e ++ ")"
    latex (Fix_ e)
        = "(\\mathbf{fix'}\\ " ++ latex e ++ ")"
    latex (Nil t)
        = "(\\varepsilon:" ++ latex t ++ ")"
    latex (Cons e1 e2)
        = "(" ++ latex e1 ++ " :: " ++ latex e2 ++ ")"
    latex (Case e1 e2 x1 x2 e3)
        = "(\\mathbf{case}\\ " ++ latex e1 ++ "\\ \\mathbf{of}\\ \\begin{Bmatrix} \\varepsilon & \\mapsto & "
            ++ latex e2 ++ "\\\\ x_{" ++ show x1 ++ "}::x_{" ++ show x2 ++ "} & \\mapsto & "
            ++ latex e3 ++ "\\end{Bmatrix})"
            
instance Latex ElabTm where
    latex (Var' x)
        = "x_{" ++ show x ++ "}"
    latex (Abs' x t exn e)  
        = "(\\lambda x_{" ++ show x ++ "}:" ++ latex t ++ "\\ \\&\\ " ++ latex exn ++ "." ++ latex e ++ ")"
    latex (AnnAbs x k e)  
        = "(\\Lambda e_{" ++ show x ++ "}:" ++ latex k ++ "." ++ latex e ++ ")"
    latex (App' e1 e2)
        = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (AnnApp e1 e2)
        = "(" ++ latex e1 ++ "\\ ⦉" ++ latex e2 ++ "⦊)"
    latex (Con' True)
        = "\\mathbf{true}"
    latex (Con' False)
        = "\\mathbf{false}"
    latex (BinOp' e1 e2)
        = "(" ++ latex e1 ++ "\\ \\oplus\\ " ++ latex e2 ++ ")"
    latex (If' e1 e2 e3)
        = "(\\mathbf{if}\\ " ++ latex e1 ++ "\\ \\mathbf{then}\\ " ++ latex e2
            ++ "\\ \\mathbf{else}\\ " ++ latex e3 ++ ")"
    latex (Crash' l t)  
        = "⚡^{\\mathrm{" ++ l ++ "}}_{" ++ latex t ++ "}"
    latex (Seq' e1 e2)
        = "(" ++ latex e1 ++ "\\ \\mathbf{seq}\\ " ++ latex e2 ++ ")"
    latex (Fix'_ e)
        = "(\\mathbf{fix'}\\ " ++ latex e ++ ")"
    latex (Fix' x ty exn e)
        = "(\\mathbf{fix}\\ x_{" ++ show x ++ "}:" ++ latex ty ++ "\\ \\&\\ " ++ latex exn ++ "." ++ latex e ++ ")"
    latex (Nil' t)
        = "(\\varepsilon:" ++ latex t ++ ")"
    latex (Cons' e1 e2)
        = "(" ++ latex e1 ++ " :: " ++ latex e2 ++ ")"
    latex (Case' e1 e2 x1 x2 e3)
        = "(\\mathbf{case}\\ " ++ latex e1 ++ "\\ \\mathbf{of}\\ \\begin{Bmatrix} \\varepsilon & \\mapsto & "
            ++ latex e2 ++ "\\\\ x_{" ++ show x1 ++ "}::x_{" ++ show x2 ++ "} & \\mapsto & "
            ++ latex e3 ++ "\\end{Bmatrix})"

-- | Types

data Ty
    = Bool                      -- TODO: Base
    | Int
    | Ty :-> Ty
    | List Ty
    deriving (Eq, Read, Show)

instance Latex Ty where
    latex Bool
        = "\\textbf{bool}"
    latex Int
        = "\\textbf{int}"
    latex (t1 :-> t2) 
        = "\\left(" ++ latex t1 ++ " \\rightarrow " ++ latex t2 ++ "\\right)"
    latex (List t)
        = "\\left[" ++ latex t ++ "\\right]"

data Kind = EXN | Kind :=> Kind
    deriving (Eq, Read, Show)
    
instance Latex Kind where
    latex EXN         = "\\mathrm{\\scriptsize EXN}"
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
    = ExnEmpty                  -- TODO: alternatively, give it a kind
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

exnNormalize :: Exn -> Exn                    -- FIXME: replace by simplifyExn
exnNormalize = lu2exn . LU.normalize . exn2lu

instance Latex Exn where
    latex (ExnEmpty)       = "\\emptyset"
    latex (ExnUnion e1 e2) = "(" ++ latex e1 ++ "\\cup " ++ latex e2 ++ ")"
    latex (ExnCon lbl)     = "\\{\\mathrm{" ++ lbl ++ "}\\}"
    latex (ExnVar n)       = "e_{" ++ show n ++ "}"
    latex (ExnApp e1 e2)   = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (ExnAbs n k e)   = "(\\lambda e_{" ++ show n ++ "}:" ++ latex k ++ "." ++ latex e ++ ")"
    
    latexColor cenv exn@(ExnVar n)
        = colorByNumber cenv n (latex exn)
    latexColor cenv (ExnUnion e1 e2)
        = "(" ++ latexColor cenv e1 ++ "\\cup " ++ latexColor cenv e2 ++ ")"
    latexColor cenv (ExnApp e1 e2)
        = "(" ++ latexColor cenv e1 ++ "\\ " ++ latexColor cenv e2 ++ ")"
    latexColor cenv (ExnAbs n k e)
        = "(\\lambda " ++ colorLatex Orange ("e_{" ++ show n ++ "}") ++ ":"
            ++ latex k ++ "." ++ latexColor ((n, Orange) : cenv) e ++ ")"
    latexColor cenv exn
        = latex exn
    
data ExnTy
    = ExnForall Name Kind ExnTy
    | ExnBool                           -- TODO: ExnBase
    | ExnInt
    | ExnList ExnTy Exn
    | ExnArr  ExnTy Exn ExnTy Exn
    deriving (Read, Show)

-- * Underlying type

underlying :: ExnTy -> Ty
underlying (ExnForall _ _ t)  = underlying t
underlying (ExnBool)          = Bool
underlying (ExnInt)           = Int
underlying (ExnList t _)      = List (underlying t)
underlying (ExnArr t1 _ t2 _) = underlying t1 :-> underlying t2

-- * Sanity checking

checkExnTy :: KindEnv -> ExnTy -> Bool
checkExnTy env (ExnForall e k t)
    | Just _ <- lookup e env = False {- shadowing -}
    | otherwise = checkExnTy ((e,k):env) t
checkExnTy env ExnBool
    = True
checkExnTy env ExnInt
    = True
checkExnTy env (ExnList t exn)
    = checkExnTy env t && checkExn env exn == Just EXN
checkExnTy env (ExnArr t1 exn1 t2 exn2)
    = checkExnTy env t1 && checkExn env exn1 == Just EXN
        && checkExnTy env t2 && checkExn env exn2 == Just EXN

checkExn :: KindEnv -> Exn -> Maybe Kind
checkExn env (ExnEmpty)
    = return EXN
checkExn env (ExnUnion exn1 exn2)
    = do k1 <- checkExn env exn1
         k2 <- checkExn env exn2
         if k1 == k2 then
            return k1
         else
            Nothing {- kind error -}
checkExn env (ExnCon lbl)
    = return EXN
checkExn env (ExnVar x)
    = lookup x env
checkExn env (ExnApp exn1 exn2)
    = do k1 <- checkExn env exn1
         k2 <- checkExn env exn2
         case k1 of
            (k1' :=> k1'') | k1' == k2 -> return k1''
            _                          -> Nothing {- kind error -}
checkExn env (ExnAbs e k exn)
    | Just _ <- lookup e env = Nothing {- shadowing -}
    | otherwise              = do k' <- checkExn ((e,k):env) exn
                                  return (k :=> k')

-- * Type simplification (reduction)

simplifyExnTy :: KindEnv -> ExnTy -> ExnTy
simplifyExnTy env (ExnForall e k t)
    = ExnForall e k (simplifyExnTy ((e,k):env) t)
simplifyExnTy env ExnBool
    = ExnBool
simplifyExnTy env ExnInt
    = ExnInt
simplifyExnTy env (ExnList t exn)
    = ExnList (simplifyExnTy env t) (simplifyExn env exn)
simplifyExnTy env (ExnArr t1 exn1 t2 exn2)
    = ExnArr (simplifyExnTy env t1) (simplifyExn env exn1)
             (simplifyExnTy env t2) (simplifyExn env exn2)
             
simplifyExn :: KindEnv -> Exn -> Exn    -- FIXME: why didn't we need the environment?
simplifyExn _env = exnNormalize

-- * Equality tests

exnTyEq :: KindEnv -> ExnTy -> ExnTy -> Bool
exnTyEq env (ExnForall e k t) (ExnForall e' k' t')
    = k == k' && exnTyEq ((e,k) : env) t (substExnTy e' e t')
exnTyEq env ExnBool ExnBool
    = True
exnTyEq env ExnInt ExnInt
    = True
exnTyEq env (ExnList t exn) (ExnList t' exn')
    = exnTyEq env t t' && exnEq env exn exn'
exnTyEq env (ExnArr t1 exn1 t2 exn2) (ExnArr t1' exn1' t2' exn2')
    = exnTyEq env t1 t1' && exnEq env exn1 exn1'
        && exnTyEq env t2 t2' && exnEq env exn2 exn2'
exnTyEq env _ _
    = False
    
-- * Checking of subtyping and subeffecting

isSubeffect :: KindEnv -> Exn -> Exn -> Bool
isSubeffect env ann1 ann2 = exnEq env (ExnUnion ann1 ann2) ann2

isSubtype :: KindEnv -> ExnTy -> ExnTy -> Bool
isSubtype env ExnBool ExnBool = True
isSubtype env ExnInt  ExnInt  = True
isSubtype env (ExnArr ty1 ann1 ty2 ann2) (ExnArr ty1' ann1' ty2' ann2')
    = isSubtype env ty1' ty1 && isSubeffect env ann1' ann1
        && isSubtype env ty2 ty2' && isSubeffect env ann2 ann2'
isSubtype env (ExnList ty ann) (ExnList ty' ann')
    = isSubtype env ty ty' && isSubeffect env ann ann'
isSubtype env (ExnForall e k ty) (ExnForall e' k' ty')
    = k == k' && isSubtype ((e,k):env) ty (substExnTy e' e ty')

instance Latex ExnTy where
    latex (ExnForall e k t)
        = "\\left(\\forall e_{" ++ show e ++ "}::" ++ latex k ++ "." ++ latex t ++ "\\right)"
    latex (ExnBool)
        = "\\mathbf{bool}"
    latex (ExnInt)
        = "\\mathbf{int}"
    latex (ExnList t exn)
        = "\\left[" ++ latex t ++ "\\langle " ++ latex exn ++ "\\rangle\\right]"
    -- TODO: print top-level annotation on the arrow for readability
    latex (ExnArr t1 exn1 t2 exn2)
        = "\\left(" ++ latex t1 ++ "\\langle " ++ latex exn1 ++ "\\rangle \\rightarrow "
              ++ latex t2 ++ "\\langle " ++ latex exn2 ++ "\\rangle \\right)"

-- | Free exception variables

fevExn :: Exn -> [Name]
fevExn (ExnEmpty)       = []
fevExn (ExnUnion e1 e2) = fevExn e1 ++ fevExn e2
fevExn (ExnVar e)       = [e]
fevExn (ExnCon c)       = []
fevExn (ExnApp e1 e2)   = fevExn e1 ++ fevExn e2
fevExn (ExnAbs n k e)   = delete n (fevExn e)

fevExnTy :: ExnTy -> [Name]
fevExnTy (ExnForall e k t)
    = delete e (fevExnTy t)
fevExnTy (ExnBool)
    = []
fevExnTy (ExnInt)
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
    -- FIXME: check for possibility of variable capture
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
substExnTy e e' (ExnInt)
    = ExnInt
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
substExn' subst (ExnCon c)
    = ExnCon c
substExn' subst (ExnAbs x k e)
    = let fvs = concatMap (\(_,exn) -> fevExn exn) subst
       in if x `elem` fvs then
            -- FIXME: alpha-rename to avoid capture
            error "substExn': variable captured"
          else
            ExnAbs x k (substExn' (deleteKey x subst) e)
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
    = let fvs = concatMap (\(_,exn) -> fevExn exn) subst
       in if e `elem` fvs then
            substExnTy' subst $
                ExnForall (e+1000) k (substExnTy' [(e,ExnVar (e+1000))] t)
          else
            ExnForall e k (substExnTy' (deleteKey e subst) t)
substExnTy' subst (ExnBool)
    = ExnBool
substExnTy' subst (ExnInt)
    = ExnInt
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
