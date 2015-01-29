module Analysis.Infer.Types where

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.Completion as C

import qualified Data.Map            as M

-- | Environments

type Env = [(Name, (ExnTy, Exn))]

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- | Reconstruction

type Result       = (ExnTy, Exn, KindEnv)
type Complete'    = (C.Complete, ExnTy, Exn, C.Env)
type Reconstruct' = (Reconstruct, ExnTy, Exn, KindEnv)
type Instantiate' = (ExnTy, KindEnv)

data Reconstruct
    = ReconstructVar   Env KindEnv Expr
                       ExnTy Exn
                       Result
    | ReconstructAbs   Env KindEnv Expr
                       Complete' Env Reconstruct' ExnTy
                       Result
    | ReconstructApp   Env KindEnv Expr
                       Reconstruct' Reconstruct' Instantiate' Subst Subst
                       Result
    | ReconstructCon   Env KindEnv Expr
                       Result
    | ReconstructBinOp Env KindEnv Expr
                       Reconstruct' Reconstruct'
                       Result
    | ReconstructIf    Env KindEnv Expr
                       Reconstruct' Reconstruct' Reconstruct' ExnTy
                       Result
    | ReconstructCrash Env KindEnv Expr
                       Complete'
                       Result
    | ReconstructSeq   Env KindEnv Expr
                       Reconstruct' Reconstruct'
                       Result
    | ReconstructFix   Env KindEnv Expr
                       Reconstruct' Instantiate' Subst Subst ExnTy Exn
                       Result
    | ReconstructNil   Env KindEnv Expr
                       Complete'
                       Result
    | ReconstructCons  Env KindEnv Expr
                       Reconstruct' Reconstruct' ExnTy
                       Result
    | ReconstructCase  Env KindEnv Expr
                       Reconstruct' Reconstruct' Env Reconstruct' ExnTy
                       Result
