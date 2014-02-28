{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Common (
    -- Syntax
    Name(), augment, only, Lbl,
    Expr(..), Con(..), ExnC(..), Op(..), freshIdents, name, fromName,
    _f, _x, _xs, _y, _ys, _z, _zs, _a, _as, _k, _id, _const,
    -- LaTeX
    LaTeX(..), command, maybeColor, space, align, newline, newpage,
    mathbf, section, subsection, subsubsection,
    gather, latexSet, latexMap, preamble, postamble
) where

import qualified Data.List  as L
import qualified Data.Map   as M
import           Data.Maybe
import qualified Data.Set   as S

-- | Names and Labels

newtype Name = Name String deriving (Eq, Ord, Show)

augment :: String -> Name -> Name
augment prefix (Name name') = Name (prefix ++ name')

only :: String -> S.Set Name -> S.Set Name
only tag = S.filter (\(Name name) -> take (length tag) name == tag)

type Lbl = String   -- FIXME: primarily used for debugging, but we will
                    -- eventually need something like this for error reporting

-- * Predefined names for Main

name :: String -> Name
name = Name

fromName :: Name -> String
fromName (Name name) = name

_f, _x, _xs, _y, _ys, _z, _zs, _a, _as, _k, _id, _const :: Name
_f     = Name "f"
_x     = Name "x"
_xs    = Name "xs"
_y     = Name "y"
_ys    = Name "ys"
_z     = Name "z"
_zs    = Name "zs"
_a     = Name "a"
_as    = Name "as"
_k     = Name "k"
_id    = Name "id"
_const = Name "const"

-- | Abstract Syntax

data Expr
    = Var Name
    | Con Con
    | Abs Name Expr
    | Fix Name Expr
    | App Expr Expr
    | Let Name Expr Expr
    | If  Lbl  Expr Expr Expr
    -- Operators
    | Op  Op   Expr Expr
    -- Pairs
    | Pair Expr Expr
    | Fst  Expr
    | Snd  Expr
    -- Lists
    | Nil
    | Cons Expr Expr
    | Case Lbl  Expr (Maybe Expr) (Maybe (Name, Name, Expr))
    deriving (Eq, Ord, Show)
    
data Con
    = Unit
    | Bool Bool
    | Int  Int
    | ExnC Lbl  ExnC
    deriving (Eq, Ord, Show)
    
data ExnC
    = Crash
    | Diverge
    | PatternMatchFail
    deriving (Eq, Ord, Show)

data Op
    = LEQ
    | ADD
    deriving (Eq, Ord, Show)
    
-- | Fresh variables

freshIdents :: [Name]
freshIdents = map (\n -> Name $ "_{" ++ show n ++ "}") [(1::Int)..]
    
-- | Pretty Printing

class LaTeX a where
    latex :: a -> String

command :: String -> String -> String
command cmd arg = "\\" ++ cmd ++ "{" ++ arg ++ "}"

maybeColor :: Maybe String -> String -> String
maybeColor Nothing      arg = arg
maybeColor (Just color) arg = "{\\color{" ++ color ++ "}" ++ arg ++ "}"

space, align, newline, newpage :: String
space   = "\\ "
align   = " & "
newline = "\\\\"
newpage  = "\\newpage "

mathbf, section, subsection, subsubsection :: String -> String
mathbf        = command "mathbf"
section       = command "section"
subsection    = command "subsection"
subsubsection = command "subsubsection"

gather :: (LaTeX a) => a -> String
gather  body = "\\begin{gather*}\n" ++ latex body ++ "\n\\end{gather*}\n"

latexSet :: LaTeX a => S.Set a -> String
latexSet s = "\\left\\{" ++ L.intercalate ", " (map latex (S.toList s)) ++ "\\right\\}"

latexMap :: (LaTeX a, LaTeX k) => M.Map k a -> String
latexMap m
    | M.null m  = "\\epsilon"
    | otherwise = L.intercalate newline
                  . map (\(k, v) -> latex k ++ align ++ "\\mapsto " ++ latex v)
                  . M.toList $ m
    
instance (LaTeX a, LaTeX b) => LaTeX (a, b) where
    latex (x, y) = "\\left(" ++ latex x ++ ", " ++ latex y ++ "\\right)"

instance LaTeX String where
    latex s = s

instance LaTeX Name where
    latex (Name name') = name'

instance LaTeX Expr where
    latex (Con c)
        = latex c
    latex (Var x) 
        = latex x
    latex (Abs x e)
        = "\\left(\\lambda " ++ latex x ++ "." ++ space ++ latex e ++ "\\right)"
    latex (App e1 e2) 
        = "\\left(" ++ latex e1 ++ space ++ latex e2 ++ "\\right)"
    latex (Let x e1 e2) 
        =  "\\left("
        ++ mathbf "let" ++ space ++ latex x  ++ space
        ++ mathbf "="   ++ space ++ latex e1 ++ space
        ++ mathbf "in"  ++ space ++ latex e2
        ++ "\\right)"
    latex (Fix f e) 
        = "\\left(" ++ mathbf "fix" ++ space ++ latex f
          ++ "." ++ space ++ latex e ++ "\\right)"
    latex (If lbl e0 e1 e2)
        = "\\left("
        ++ mathbf "if"   ++ "_{" ++ lbl ++ "}" ++ space ++ latex e0 ++ space
        ++ mathbf "then"                       ++ space ++ latex e1 ++ space
        ++ mathbf "else"                       ++ space ++ latex e2
        ++ "\\right)"
    -- Operators
    latex (Op op e1 e2)
        = "\\left(" ++ latex e1 ++ latex op ++ latex e2 ++ "\\right)"
    -- Pair
    latex (Pair e1 e2)
        = "\\left(" ++ latex e1 ++ ", " ++ latex e2 ++ "\\right)"
    latex (Fst e)
        = "\\left(" ++ mathbf "fst" ++ space ++ latex e ++ "\\right)"
    latex (Snd e)
        = "\\left(" ++ mathbf "snd" ++ space ++ latex e ++ "\\right)"
    -- Lists
    latex Nil
        = mathbf "[]"
    latex (Cons e1 e2)
        = "\\left(" ++ latex e1 ++ space ++ mathbf "::" ++ space ++ latex e2 ++ "\\right)"
    latex (Case lbl e arm1 arm2)
        = "\\left("
          ++ mathbf "case" ++ "_{" ++ lbl ++ "}" ++ space ++ latex e ++ space
          ++ mathbf "of" ++ space ++ "\\left\\{"
          ++ maybe "" (\e1 -> mathbf "[]" ++ "\\to " ++ latex e1) arm1
          ++ (if isJust arm1 && isJust arm2 then "; " else "")
          ++ maybe "" (\(x, xs, e2) -> "\\left(" ++ latex x ++ "::"
                                                 ++ latex xs ++ "\\right)"
                                                 ++ "\\to " ++ latex e2) arm2
          ++ "\\right\\}" ++ "\\right)"

instance LaTeX Con where
    latex (Bool     True ) = mathbf "True"
    latex (Bool     False) = mathbf "False"
    latex (Int      n    ) = mathbf (show n)
    latex (ExnC lbl exnc ) = latex exnc ++ "_{" ++ lbl ++ "}"

instance LaTeX ExnC where
    latex Crash            = "\\lightning "
    latex Diverge          = "\\bot "
    latex PatternMatchFail = "\\clubsuit "

instance LaTeX Op where
    latex LEQ = "\\leq "
    latex ADD = " + "

preamble, postamble :: String
preamble  =  "\\documentclass{article}\n"
          ++ "\\usepackage{amsfonts}\n"
          ++ "\\usepackage[fleqn]{amsmath}\n"
          ++ "\\usepackage{amssymb}\n"
          ++ "\\usepackage[paperwidth=300cm,paperheight=400cm]{geometry}\n"
          ++ "\\usepackage[cm]{fullpage}\n"
          ++ "\\usepackage{stmaryrd}\n"
          ++ "\\usepackage[usenames,dvipsnames]{xcolor}\n"
          ++ "\\begin{document}\n"

postamble = "\\end{document}"
