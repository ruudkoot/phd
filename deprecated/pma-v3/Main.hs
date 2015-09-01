{-# LANGUAGE MultiWayIf #-}

module Main where

import System.IO
import System.Process

import Control.Monad
import Control.Monad.State

import qualified Data.Graph      as G
import qualified Data.Graph.Util as G
import qualified Data.List       as L
import qualified Data.Map        as M
import qualified Data.Map.Util   as M
import           Data.Maybe
import qualified Data.Set        as S
import qualified Data.Set.Util   as S
import qualified Data.Tree       as T
import           Data.Tuple.Util

import Subst
import Syntax
import Semantics
import Types     hiding (main)
import Shapes
import Constr
import Analysis
import Ref                          -- unused
import Exn
import Examples

-- | Main

-- * Type inference

testTypes :: IO ()
testTypes = do
    let ((s, t, e'), _) = runState (infer M.empty exR1) freshIdents
    putStrLn $ "t = " ++ show t
    putStrLn $ "e = " ++ show e'

-- * Analysis

main :: IO ()
main = do
    mapM_ (\(desc,e) -> testcase desc e) allExamples

testcase :: String -> Expr () -> IO ()
testcase desc e = do

    putStrLn $ "== " ++ desc ++ " " ++ replicate (76 - length desc) '='

    -- SEMANTICS
    
    let (eT, freshIdents2) = runState (transform e) freshIdents
    -- putStrLn $ show e
    -- putStrLn $ show eT
    -- putStrLn $ "boundVariablesDistinct e = " ++ show (boundVariablesDistinct e)
    -- putStrLn $ "boundVariablesDistinct eT = " ++ show (boundVariablesDistinct eT)
    let (_heap1, z1) = evalState (reduce        10000 M.empty eT) freshIdents2
    let (_heap2, z2) = evalState (reduceFurther 10000 M.empty eT) freshIdents2
    let ev1@(evRef1, evExn1) = postProcessEval1 z1
    let ev2@(evRef2, evExn2) = postProcessEval2 z2
    putStrLn $ "ev1 = " ++ show ev1
    putStrLn $ "ev2 = " ++ show ev2

    -- TYPE INFERENCE
    let ((s, t, e'), freshIdents1) = runState (infer M.empty e) freshIdents
    --putStrLn $ "s = " ++ show s
    putStrLn $ "t = " ++ show t
    --putStrLn $ "e' = " ++ show e'
    let se' = s $@ e'
    --putStrLn $ "se' = " ++ show se'

    -- REFINEMENTS
    let (((rt, rc, cx), re'), freshIdents2) = runState (analyze M.empty se') freshIdents1
    putStrLn $ "rt = " ++ show rt
    --putStrLn $ "rc = " ++ show rc
    --putStrLn $ "re' = " ++ show re'
    -- Constraints decomposed (but not sets of constants)
    let rd = decompose rc
    --putStrLn $ "rd = " ++ show rd
    
    -- EXCEPTIONS
    let dx = decompose cx
    --putStrLn $ "dx = " ++ show dx
    
    -- TESTING OF CONSTRAINT SOLVING
    
    -- let unitSol = error "Solution ()" :: Solution ()
    
    --putStrLn $ "dependency map = " ++ show (buildDependencyMap rd)
    let rs = solveRef rd
    --putStrLn $ "solve = " ++ show rs
    putStrLn $ "validateSolution (ref) = " ++ show (validateSolution rd rs rs)
    
    --putStrLn $ "dependency map (exn) = " ++ show (buildDependencyMap dx)
    let sx = solveExn dx rs
    --putStrLn $ "solve (exn) = " ++ show sx
    putStrLn $ "validateSolution (exn) = " ++ show (validateSolution dx rs sx)
    
    putStrLn $ "rt (ref) = " ++ showSolved rs rt
    putStrLn $ "rt (exn) = " ++ showSolved sx rt
    let cvRef2 = collect rs rt
    let cvExn2 = collect sx rt
    putStrLn $ "evRef2 = " ++ show evRef2   -- FIXME: we're interested in
    putStrLn $ "cvRef2 = " ++ show cvRef2   --        complete shapes here.
    putStrLn $ "evExn2 = " ++ show evExn2
    putStrLn $ "cvExn2 = " ++ show cvExn2
    putStrLn $ "precision (ref) = " ++ (
            if | evRef2 == cvRef2             -> "exact"
               | evRef2 `S.isSubsetOf` cvRef2 -> "SOUND BUT IMPRECISE"
               | otherwise                    -> error "UNSOUND"
        )
    putStrLn $ "precision (exn) = " ++ (
            if | evExn2 == cvExn2             -> "exact"
               | evExn2 `S.isSubsetOf` cvExn2 -> "SOUND BUT IMPRECISE"
               | otherwise                    -> error "UNSOUND"
        )
    
    -- ENVIRONMENTS
    let env = collectEnvs re'
    --putStrLn $ "env = " ++ show env
    --putStrLn $ "env (ref, solved) = " ++ showSolved rs env
    --putStrLn $ "env (exn, solved) = " ++ showSolved sx env
    
    -- VISUALIZATION
    let viz = graphviz rt rd rs dx sx
    --putStrLn $ viz
    writeFile ("dot/" ++ desc ++ ".dot") viz 
    --runCommand ("dot -Tpng -o \"dot/" ++ desc ++ ".png\" \"dot/" ++ desc ++ ".dot\"")
    
    return ()

-- | Verification helpers (move the somewhere more appropriate)

-- * Collect names from inside constructors (but not abstractions)

collectNF :: Sh -> S.Set Name
collectNF (ShBase n)
    = S.singleton n
collectNF (ShFun _sh1 _sh2 n)
    = S.singleton n
collectNF (ShPair sh1 sh2 n)
    = S.singleton n `S.union` collectNF sh1 `S.union` collectNF sh2
collectNF (ShList sh n)
    = S.singleton n `S.union` collectNF sh

-- * Collect exceptions

collect :: Ord a => Solution a -> Sh -> S.Set a
collect sol sh
    = S.foldr 
        (\n r -> (M.findWithDefault S.empty n sol) `S.union` r) 
        S.empty
        (collectNF sh)
