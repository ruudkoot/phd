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

-- * Declarative type system

type JudgeType   = (Env, KindEnv, ElabTm, ExnTy, Exn)
type JudgeKind   = (KindEnv, Exn, Kind)
type JudgeSubTy  = (KindEnv, ExnTy, ExnTy)
type JudgeSubEff = (KindEnv, Exn, Exn)

data DerivType
    = TypeVar                                                          JudgeType
    | TypeCon                                                          JudgeType
    | TypeCrash                                                        JudgeType
    | TypeAbs                            DerivType                     JudgeType
    | TypeAnnAbs                         DerivType                     JudgeType
    | TypeApp                            DerivType DerivType           JudgeType
    | TypeAnnApp JudgeKind               DerivType                     JudgeType
    | TypeFix    JudgeSubEff JudgeSubEff DerivType                     JudgeType
    | TypeOp                             DerivType DerivType           JudgeType
    | TypeSeq                            DerivType DerivType           JudgeType
    | TypeIf                             DerivType DerivType DerivType JudgeType
    | TypeNil                                                          JudgeType
    | TypeCons                           DerivType DerivType           JudgeType
    | TypeCase   JudgeSubEff             DerivType DerivType DerivType JudgeType
    | TypeSub    JudgeSubTy  JudgeSubEff DerivType                     JudgeType
    
getJT :: DerivType -> JudgeType
getJT (TypeVar            jt) = jt
getJT (TypeCon            jt) = jt
getJT (TypeCrash          jt) = jt
getJT (TypeAbs    _       jt) = jt
getJT (TypeAnnAbs _       jt) = jt
getJT (TypeApp    _ _     jt) = jt
getJT (TypeAnnApp _ _     jt) = jt
getJT (TypeFix    _ _ _   jt) = jt
getJT (TypeOp     _ _     jt) = jt
getJT (TypeSeq    _ _     jt) = jt
getJT (TypeIf     _ _ _   jt) = jt
getJT (TypeNil            jt) = jt
getJT (TypeCons   _ _     jt) = jt
getJT (TypeCase   _ _ _ _ jt) = jt
getJT (TypeSub    _ _ _   jt) = jt

-- * Syntax-directed elaboration

type JudgeElab   = (Env, KindEnv, Expr, ElabTm, ExnTy, Exn)
type JudgeTyWff  = (KindEnv, ExnTy, Ty)

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
type Reconstruct'   = ((DerivType, DerivElab, Reconstruct), ElabTm, ExnTy, Exn)
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
