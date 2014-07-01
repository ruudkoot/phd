module Main where

import Data.List (intersperse, nub)
import Data.Set (toList)

import Util
import Util.List

import Language.Haskell.Exts.Annotated

import Common
import TCMonad
import TypeInference
import Refinement
import PrintType

import Solver.Unification
                               
-- | Main

main = do let fileName = "../sample/In.hs"
          contents <- readFile fileName
          let parseResult = parseModuleWithMode defaultParseMode contents
          case parseResult of
            ParseOk hModule            
                -> do putStrLn "==============================================="
                
                      let ( R { _ty = ty, _cs = c, _rc = rc }, l)
                            = analyzeMain hModule

                      putStrLn $ listPerLine $ l
                      
                      putStrLn "==============================================="

            ParseFailed srcLoc message
                -> do print srcLoc
                      print message
                      
showConstrSet rcs = "(" ++ concat (intersperse ", " (map (init . show) rcs)) ++ ")"

-- * Analysis

analyzeMain :: (Ord l, Show l) => Module l -> (R, [String])
analyzeMain (Module _ _ _ _ topLevel)
    = let (patBinds, dataDecls) = splitTopLevel topLevel
          constructorEnv        = [] --concatMap dataDeclType dataDecls
          topLevelBindings      = Let undefined (BDecls undefined patBinds) (Var undefined (UnQual undefined (Ident undefined "main")))
       in let (x, st) = runTC (typeInfer ({-builtinConstructors ++ -}constructorEnv) topLevelBindings)
           in (x, TCMonad.log st)

-- * Split top-level declarations into bindings and data type declarations

splitTopLevel :: [Decl l] -> ([Decl l], [Decl l])
splitTopLevel [] = ([],[])
splitTopLevel (d@(DataDecl _ _ _ _ _ _):decls)
    = let (ps, ds) = splitTopLevel decls in (ps, d:ds)
splitTopLevel (p@(PatBind _ _ _ _ _):decls)
    = let (ps, ds) = splitTopLevel decls in (p:ps, ds)
