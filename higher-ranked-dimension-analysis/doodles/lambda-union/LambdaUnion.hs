module LambdaUnion where

type Name = String

data Base
    = ANN
    | EFF
    deriving (Eq, Show)
    
data Con
    = Ann Integer
    | Eff Integer Integer
    deriving (Eq, Show)

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
    show (Var x) = x
    show (Con c) = "{" ++ show c ++ "}"
    show (Abs x ty tm) = "(λ" ++ x ++ ":" ++ show ty ++ "." ++ show tm ++ ")"
    show (App tm1 tm2) = show tm1 ++ " " ++ show tm2

instance Show Ty where
    show (ty1 :-> ty2) = show ty1 ++ " -> " ++ show ty2
    show (Base b) = show b
