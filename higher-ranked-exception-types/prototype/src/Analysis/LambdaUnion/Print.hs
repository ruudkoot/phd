module Analysis.LambdaUnion.Print where

import Analysis.Latex

import Analysis.LambdaUnion.Syntax

instance Latex Sort where
    latex C           = "C"
    latex (s1 :=> s2) = "(" ++ latex s1 ++ "\\Rightarrow " ++ latex s2 ++ ")"



instance Show a => Show (Tm a) where
    show (Var   x    ) = "x" ++ show x
    show (Con   c    ) = "{" ++ show c ++ "}"
    show (Abs   x s e) = "(λx" ++ show x ++ ":" ++ show s ++ "." ++ show e ++ ")"
    show (App   e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Union e1 e2) = "(" ++ show e1 ++ "∪" ++ show e2 ++ ")"
    show (Empty      ) = "∅"

instance Latex a => Latex (Tm a) where
    latex (Var   x    )
        = "x_{" ++ show x ++ "}"
    latex (Con   c    )
        = "\\{" ++ latex c ++ "\\}"
    latex (Abs   x s e)
        = "(\\lambda x_{" ++ show x ++ "}:" ++ latex s ++ "." ++ latex e ++ ")"
    latex (App   e1 e2) 
        = "(" ++ latex e1 ++ "\\ " ++ latex e2 ++ ")"
    latex (Union e1 e2)
        = "(" ++ latex e1 ++ "\\cup" ++ latex e2 ++ ")"
    latex (Empty      )
        = "\\emptyset"

