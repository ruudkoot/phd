{-# LANGUAGE OverloadedStrings, ViewPatterns #-}

-- TODO: use right-to-left syntax for environments to avoid headaches.
-- TODO: pretty print types
-- NOTE: fresh variable are generated in an order that results in nice types

module Analysis.Completion where

import Text.Blaze.Html5 (ToMarkup)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import Analysis.Names
import Analysis.Common
import Analysis.Print

-- | Types

-- * Environments

type Env = [(Name, Kind)]

-- * Derivation tree

data Complete
    = CompleteBool Env                   Ty ExnTy Exn Env
    | CompleteInt  Env                   Ty ExnTy Exn Env
    | CompleteList Env Complete          Ty ExnTy Exn Env
    | CompleteArr  Env Complete Complete Ty ExnTy Exn Env

(#) :: (ExnTy -> Exn -> Env -> Complete)
            -> (ExnTy, Exn, Env) -> (Complete, ExnTy, Exn, Env)
x # (y1, y2, y3) = (x y1 y2 y3, y1, y2, y3)

-- | Completion

complete' :: Env -> Ty -> (Complete, ExnTy, Exn, Env)
complete' env ty = evalFresh (complete env ty) 1

complete :: Env -> Ty -> Fresh (Complete, ExnTy, Exn, Env)
complete env0 ty@Bool = do
    e <- fresh
    return $ CompleteBool env0 ty #
           (ExnBool
           ,exnFromEnv (ExnVar e) env0
           ,[(e, kindFromEnv env0)])
complete env0 ty@Int = do
    e <- fresh
    return $ CompleteInt env0 ty #
           (ExnInt
           ,exnFromEnv (ExnVar e) env0
           ,[(e, kindFromEnv env0)])
complete env0 ty@(List t) = do
    e <- fresh
    (dt', t', exn, env1) <- complete env0 t
    return $ CompleteList env0 dt' ty #
           (ExnList t' exn
           ,exnFromEnv (ExnVar e) env0
           ,env1 ++ [(e, kindFromEnv env0)])
complete env0 ty@(t1 :-> t2) = do
    (dt1', t1', exn1, env1) <- complete [] t1 -- fully-flexible = in any context
    e <- fresh
    (dt2', t2', exn2, env2) <- complete (env1 ++ env0) t2
    return $ CompleteArr env0 dt1' dt2' ty #
           (forallFromEnv env1 (ExnArr t1' exn1 t2' exn2)
           ,exnFromEnv (ExnVar e) env0
           ,env2 ++ [(e, kindFromEnv env0)])

-- * Helper functions

exnFromEnv :: Exn -> Env -> Exn
exnFromEnv exn (map fst -> es) = foldr (\e r -> ExnApp r (ExnVar e)) exn es

forallFromEnv :: Env -> ExnTy -> ExnTy
forallFromEnv env exn = foldl (\r (e,k) -> ExnForall e k r) exn env

kindFromEnv :: Env -> Kind
kindFromEnv (map snd -> ks) = foldl (flip (:=>)) EXN ks

-- | Pretty printing

ltxComplete :: Env -> Ty -> ExnTy -> Exn -> Env -> H.Html
ltxComplete env ty exnTy exn env'
    = H.toHtml $ "\\[" ++ latex env ++ " \\vdash " ++ latex ty ++ " : " ++ latex exnTy ++ "\\&\\ " ++ latex exn ++ "\\triangleright " ++ latex env' ++ "\\]"

instance ToMarkup Complete where
    toMarkup (CompleteBool env ty exnTy exn env')
        = derive "C-Bool" [] (ltxComplete env ty exnTy exn env')
    toMarkup (CompleteBool env ty exnTy exn env')
        = derive "C-Int"  [] (ltxComplete env ty exnTy exn env')
    toMarkup (CompleteList env dExnTy ty exnTy exn env')
        = derive "C-List" [H.toMarkup dExnTy] (ltxComplete env ty exnTy exn env')
    toMarkup (CompleteArr env dExnTy1 dExnTy2 ty exnTy exn env')
        = derive "C-Arr" (map H.toMarkup [dExnTy1, dExnTy2])
                                              (ltxComplete env ty exnTy exn env')

