module Analysis.Infer.Types where

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.Completion as C

import qualified Data.Map            as M

-- | Environments

type Env = [(Name, (ExnTy, Exn))]

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- | Constraints

data Constr = Exn :<: Name
    deriving Show

-- | Reconstruction

type Result       = (ExnTy, Name, [Constr], KindEnv)
type Complete'    = (C.Complete, ExnTy, Exn, C.Env)
type Reconstruct' = (Reconstruct, ExnTy, Name, [Constr], KindEnv)
type Instantiate' = (ExnTy, KindEnv)

data Reconstruct
    = ReconstructVar   Env KindEnv Expr
                       ExnTy Exn Name
                       Result
    | ReconstructAbs   Env KindEnv Expr
                       Complete' Env Reconstruct' [Name] Exn ExnTy Name
                       Result
    | ReconstructApp   Env KindEnv Expr
                       Reconstruct' Reconstruct' Instantiate' Subst Subst Name [Constr]
                       Result
    | ReconstructCon   Env KindEnv Expr
                       Name
                       Result
    | ReconstructCrash Env KindEnv Expr
                       Complete'
                       Result
    | ReconstructSeq   Env KindEnv Expr
                       Reconstruct' Reconstruct' Name
                       Result
    | ReconstructFix   Env KindEnv Expr
                       Reconstruct' Instantiate' Subst Subst Name [Constr] 
                       Result
    | ReconstructNil   Env KindEnv Expr
                       Complete' Name
                       Result
    | ReconstructCons  Env KindEnv Expr
                       Reconstruct' Reconstruct' ExnTy Name Name
                       Result
    | ReconstructCase  Env KindEnv Expr
                       Reconstruct' Reconstruct' Env Reconstruct' ExnTy Name [Constr]
                       Result
