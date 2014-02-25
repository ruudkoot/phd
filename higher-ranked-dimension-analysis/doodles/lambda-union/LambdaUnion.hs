{-# LANGUAGE MultiParamTypeClasses #-}

module LambdaUnion where

import Data.Map as M (Map, delete, elems, empty, findWithDefault, singleton)
import Data.Set as S (Set, delete, empty, member, singleton, union, unions)
import System.Random

type Name = String

data Base
    = ANN
    | EFF
    deriving (Eq, Show)
    
data Con
    = Ann Integer
    | Eff Integer Integer
    deriving Eq

instance Show Con where
    show (Ann n)   = show n
    show (Eff n m) = "(" ++ show n ++ "," ++ show m ++ ")"

data Tm
    = Var Name
    | Con Con
    | Abs Name Ty Tm
    | App Tm Tm
    | Union Tm Tm

data Ty
    = Ty :-> Ty
    | Base Base

instance Show Tm where
    show (Var x)         = x
    show (Con c)         = "{" ++ show c ++ "}"
    show (Abs x ty tm)   = "(λ" ++ x ++ ":" ++ show ty ++ "." ++ show tm ++ ")"
    show (App tm1 tm2)   = show tm1 ++ " " ++ show tm2
    show (Union tm1 tm2) = show tm1 ++ "∪" ++ show tm2

instance Show Ty where
    show (ty1 :-> ty2) = "(" ++ show ty1 ++ "→" ++ show ty2 ++ ")"
    show (Base b)      = show b

-- | Free variables

class FV t where
    fv :: t -> Set Name

instance FV Tm where
    fv (Var x) = S.singleton x
    fv (Con c) = S.empty
    fv (Abs x ty tm) = S.delete x (fv tm)
    fv (App tm1 tm2) = union (fv tm1) (fv tm2)
    fv (Union tm1 tm2) = union (fv tm1) (fv tm2)
    
instance FV s => FV (Subst s) where
    fv = S.unions . map fv . M.elems . unSubst

-- | Substitutions

newtype Subst s = Subst { unSubst :: Map Name s }

(~>) :: Name -> s -> Subst s
x ~> s = Subst (M.singleton x s)

class Substitute s t where
    ($@) :: Subst s -> t -> t

instance Substitute Tm Tm where
    subst $@ Var x         = findWithDefault (Var x) x (unSubst subst)
    subst $@ Con c         = Con c
    subst $@ Abs x ty tm   =
        if S.member x (fv subst) then
            error "variable capture"
        else
            Abs x ty (Subst (M.delete x (unSubst subst)) $@ tm)
    subst $@ App tm1 tm2   = App (subst $@ tm1) (subst $@ tm2)
    subst $@ Union tm1 tm2 = Union (subst $@ tm1) (subst $@ tm2)
 
-- | Full beta-reduction

{-
fullBetaReduce :: Tm -> Tm
fullBetaReduce = fixpoint fullBetaReduce'
-}

fullBetaReduce' :: Tm -> Tm
fullBetaReduce' (App tm1 tm2) =
    case fullBetaReduce' tm1 of
        Union tm11 tm12 -> Union (fullBetaReduce' (App tm11 tm2))
                                 (fullBetaReduce' (App tm12 tm2))
        Abs x ty tm     -> fullBetaReduce' (x ~> tm2 $@ tm)
        tm1'            -> App tm1' tm2
fullBetaReduce' x = x

-- | Example terms

ex1 = App (Union (Abs "x" (Base ANN) (Var "x"))
                 (Abs "x" (Base ANN) (Union (Var "x") (Con (Ann 43))))
          ) (Con (Ann 42))
