module Analysis.Infer.Types where

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.Completion as C

import qualified Data.Map            as M

-- | Environments

type Env = [(Name, (ExnTy, Exn))]

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- | Derivation tree

type JudgeElab   = (Env, KindEnv, Expr, ElabTm, ExnTy, Exn)
type JudgeTyWff  = (KindEnv, ExnTy, Ty)
type JudgeKind   = (KindEnv, Exn, Kind)
type JudgeSubTy  = (KindEnv, ExnTy, ExnTy)
type JudgeSubEff = (KindEnv, Exn, Exn)

data DerivElab
    = ElabVar                                                          JudgeElab
    | ElabCon                                                          JudgeElab
    | ElabCrash                                                        JudgeElab
    | ElabAbs   JudgeTyWff JudgeKind               DerivElab           JudgeElab
    | ElabApp   JudgeSubTy JudgeSubEff [JudgeKind] DerivElab DerivElab JudgeElab
    | ElabFix   JudgeSubTy JudgeSubEff [JudgeKind] DerivElab           JudgeElab
    | ElabOp                                       DerivElab DerivElab JudgeElab
    | ElabSeq                                      DerivElab DerivElab JudgeElab
    | ElabIf                            DerivElab  DerivElab DerivElab JudgeElab
    | ElabNil                                                          JudgeElab
    | ElabCons                                     DerivElab DerivElab JudgeElab
    | ElabCase                          DerivElab  DerivElab DerivElab JudgeElab

-- | Reconstruction algorithm

type Result         = (ElabTm, ExnTy, Exn)
type Complete'      = (C.Complete, ExnTy, Exn, C.Env)
type Reconstruct'   = ((DerivElab, Reconstruct), ElabTm, ExnTy, Exn)
type Instantiate'   = (ExnTy, KindEnv)
type KleeneMycroft' = ([(ExnTy, Exn, ExnTy, Name, ExnTy, Exn, KindEnv,
                         Subst, Subst, ExnTy, ExnTy, Exn, Exn)], ExnTy, Exn, Subst)

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
                       Result
    | ReconstructSeq   Env KindEnv Expr
                       Reconstruct' Reconstruct'
                       Result
    | ReconstructFix   Env KindEnv Expr
                       Reconstruct' Instantiate' ExnTy Exn KleeneMycroft'
                       Result
    | ReconstructNil   Env KindEnv Expr
                       Result
    | ReconstructCons  Env KindEnv Expr
                       Reconstruct' Reconstruct' ExnTy
                       Result
    | ReconstructCase  Env KindEnv Expr
                       Reconstruct' Reconstruct' Env Reconstruct' ExnTy
                       Result
