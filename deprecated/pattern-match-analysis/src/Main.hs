module Main where

import Data.List (intersperse, nub)
import Data.Set (toList)

import Util
import Util.List

import Language.Haskell.Exts.Annotated

import Common
import TypeInference
import PatternTyping
import Refinement -- TODO: export from Common?
import Solver
import qualified AbstractInterpretation as AI

import Latex
import PrintType

                               
-- | Main

main = do let fileName = "../sample/"
                          -- ++ "Sample"
                          -- ++ "SampleFilter"
                          ++ "Thesis"
                          ++ ".hs"
          contents <- readFile fileName
          let parseResult = parseModuleWithMode defaultParseMode contents
          case parseResult of
            ParseOk hModule            
                -> do --print "== ABSTRACT SYNTAX TREE =========================="
                      --print hModule
                      
                      let R { _ty = ty
                            , _cs = c
                            , _rc = rc
                            } = analyzeMain hModule

                      print "== REFINEMENT TYPES =============================="
                      -- putStrLn $ prettyPrint ty
                      -- putStrLn "---------------------------"
                      putStrLn $ printType ty
                      putStrLn "---------------------------"
                      putStrLn $ show c
                      putStrLn "---------------------------"
                      putStr   $ listPerLine rc
                      putStrLn "---------------------------"
                      let subst = unify c
                      putStrLn $ show subst
                      putStrLn "---------------------------"
                      let checkCS = subst $@@ c
                      -- putStrLn $ show checkCS
                      putStr "Sanity check: "
                      putStrLn (if and (map (\((:=:!) _ a b) -> a == b) checkCS) then "\x1b[0;32;49mPASSED\x1b[0;30;49m" else "\x1b[0;31;49mFAILED\x1b[0;30;49m")
                      putStrLn "-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-"
                      let ty' = subst $@ ty
                      -- putStrLn $ prettyPrint $ ty'
                      -- putStrLn "---------------------------"
                      putStrLn $ printType ty'
                      putStrLn "---------------------------"
                      let rc' = subst $@< rc
                      putStr   $ listPerLine rc'
                      putStrLn "-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-"
                      putStrLn $ show $ dependencyAnalysis rc'
                      putStrLn ". . . . . . . . . . . . . ."
                      putStr   $ listPerLine $ showDG' $ dependencyAnalysis' rc'
                      putStrLn "---------------------------"
                      let ivs = inputVars Co ty'
                      let dvs = dependentVars rc' ivs
                      putStrLn $ "Input vars          : " ++ show ivs
                      putStrLn $ "Input-dependent vars: " ++ show dvs
                      putStrLn "---------------------------"
                      let (rcs1,rcs2) = partitionRCS dvs rc'
                      putStr   $ listPerLine $ rcs1
                      putStrLn ". . . . . . . . . . . . . ."
                      putStr   $ listPerLine $ rcs2
                      putStrLn "---------------------------"
                      let substRT2 = solveRT rcs2
                      putStr   $ showSubstRT substRT2
                      putStrLn "---------------------------"
                      {- L < U, U < L, or L < L && U < U?
                      putStr   $ listPerLine $ (substRT2 $@@^ rcs2)
                      putStrLn ". . . . . . . . . . . . . ."
                      putStr "Sanity check: "
                      putStrLn (if sanityCheck (substRT2 $@@^ rcs2) then "\x1b[0;32;49mPASSED\x1b[0;30;49m" else "\x1b[0;31;49mFAILED\x1b[0;30;49m")
                      putStrLn "---------------------------"
                      -}
                      {-putStr   $ listPerLine $ (substRT2 $@@^! rcs2)
                      putStrLn ". . . . . . . . . . . . . ."-}
                      putStr "Sanity check: "
                      putStrLn (if sanityCheck (substRT2 $@@^! rcs2) then "\x1b[0;32;49mPASSED\x1b[0;30;49m" else "\x1b[0;31;49mFAILED\x1b[0;30;49m")
                      {-putStrLn "---------------------------"
                      putStr   $ listPerLine $ (substRT2 $@@^? rcs2)
                      putStrLn ". . . . . . . . . . . . . ."-}
                      putStr "Sanity check: "
                      putStrLn (if sanityCheck (substRT2 $@@^? rcs2) then "\x1b[0;32;49mPASSED\x1b[0;30;49m" else "\x1b[0;31;49mFAILED\x1b[0;30;49m")
                      putStrLn "---------------------------"
                      putStrLn $ if isSatisfiable substRT2
                                 then "\x1b[0;32;49mNo pattern-match failure detected :)\x1b[0;30;49m"
                                 else "\x1b[0;31;49m>> PATTERN-MATCH FAILURE DETECTED!!! <<\x1b[0;30;49m"
                      putStrLn "---------------------------"
                      let unsolvedConstrs = nub rcs1
                      let solvedType      = TyForall (UC {uc = unsolvedConstrs}) Nothing Nothing (substRT2 `asrt` ty')
                      putStrLn $ {-showConstrSet unsolvedConstrs ++ " => " ++-} printType solvedType


{-                    print "== ABSTRACT INTERPRETATION ===================="
                      -- let ae2 = applySubst2AST subst ae
                      print $ AI.run ae
-}

            ParseFailed srcLoc message
                -> do print srcLoc
                      print message
                      
showConstrSet rcs = "(" ++ concat (intersperse ", " (map (init . show) rcs)) ++ ")"

-- * Analysis

analyzeMain :: (Ord l, Show l) => Module l -> R
analyzeMain (Module _ _ _ _ topLevel)
    = let (patBinds, dataDecls) = splitTopLevel topLevel
          constructorEnv        = concatMap dataDeclType dataDecls
          [PatBind _ (PVar _ (Ident _ "main")) _ (UnGuardedRhs _ e) _] = patBinds
       in typeInfer (builtinConstructors ++ constructorEnv) freshVars e

-- * Split top-level declarations into bindings and data type declarations

splitTopLevel :: [Decl l] -> ([Decl l], [Decl l])
splitTopLevel [] = ([],[])
splitTopLevel (d@(DataDecl _ _ _ _ _ _):decls)
    = let (ps, ds) = splitTopLevel decls in (ps, d:ds)
splitTopLevel (p@(PatBind _ _ _ _ _):decls)
    = let (ps, ds) = splitTopLevel decls in (p:ps, ds)
