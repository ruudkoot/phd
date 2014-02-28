module Parser where

import qualified Data.Map      as M
import qualified Data.Map.Util as M
import qualified Data.Set      as S
import qualified Data.Set.Util as S
import qualified Data.Graph    as G

import System.Environment

import qualified Language.Haskell.Exts as HSE
import           Syntax

desugar :: HSE.Exp -> Expr ()
desugar = undefined
