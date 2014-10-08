{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns      #-}

module Analysis.Infer where

-- TODO: reconstruct derivation tree

import           Analysis.Names
import           Analysis.Common
import qualified Analysis.LambdaUnion as LU
import qualified Analysis.Completion  as C
import           Analysis.Latex

import qualified Data.Map    as M

-- | Exception type reconstruction

-- * Environments

type Env = [(Name, (ExnTy, Exn))]

instance Latex (Name, (ExnTy, Exn)) where
    lhs2tex (show -> e, (lhs2tex -> ty, lhs2tex -> exn))
        = "e_" ++ e ++ " : " ++ ty ++ " & " ++ exn

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- * Constraints

data Constr = Exn :<: Name
    deriving Show

instance Latex Constr where
    lhs2tex (exn :<: e) = lhs2tex exn ++ " :<: e_" ++ show e

-- * Substitutions

instance Latex (Name, Exn) where
    lhs2tex (show -> e, lhs2tex -> exn)
        = "e_" ++ e ++ " -|> " ++ exn

-- * Reconstruction

debug cs fs = msg [ unlines (map f fs ++ ["\\begin{code}"] ++ cs ++ ["\\end{code}"])
    ] where f x = "%format " ++ x

-- TODO: store KindEnv, Env in the monad
reconstruct :: Env -> KindEnv -> Expr -> FreshLog Log (ExnTy, Name, [Constr], KindEnv)

reconstruct env kenv (Var x)
    = do let Just (t, exn) = lookup x env
         e <- fresh
         
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             e_" ++ show x,
            "    =  let  ty & exn = env x ~> " ++ lhs2tex t ++ " & " ++ lhs2tex exn,
            "            e_" ++ show e ++ " be fresh",
            "       in   (ty, e_" ++ show e ++ ", Set (exn :<: e_" ++ show e ++ "),"
                ++ "[e_" ++ show e ++ " : DenoteEnv exn kenv])",
            "            ~> (" ++ lhs2tex t ++ ", " ++ "e_" ++ show e
                ++ ", Set (" ++ lhs2tex exn ++ " :<: e_" ++ show e ++ "), "
                ++ lhs2tex [(e, kindOf kenv exn)] ++ ")"
          ] ["e_" ++ show e]

         return (t, e, [exn :<: e], [(e, kindOf kenv exn)])

reconstruct env kenv (Abs x ty tm)
    = do (t1', ExnVar exn1, kenv1) <- C.complete [] ty
         let env' = (x, (t1', ExnVar exn1)) : env
         (t2', exn2, c1, kenv2) <- reconstruct env' (kenv1 ++ kenv) tm
         let v = [exn1] ++ map fst kenv1 ++ fev env
         -- FIXME: is this the correct environment we are passing here?
         let exn2' = solve (kenv1 ++ [(exn1,EXN)] ++ kenv) c1 v exn2
         let t' = C.forallFromEnv kenv1 (ExnArr t1' (ExnVar exn1) t2' exn2')
         e <- fresh

         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (LAMBDA (x_" ++ show x ++ " : " ++ lhs2tex ty ++ ") ("
                ++ lhs2tex tm ++ "))",
            "    =  let  (ty'_1,  e_1,       kenv_1)  =   complete [] (" ++ lhs2tex ty ++ ")"
                ++ " ~> (" ++ lhs2tex t1' ++ ", e_" ++ show exn1 ++ ", "
                ++ lhs2tex kenv1 ++ ")",
            "            (ty'_2,  e_2, C_1,  kenv_2)  =   reconstruct ("
                ++ lhs2tex [(x, (t1', ExnVar exn1))] ++ " ++ env) (kenv_1 ++ kenv) ("
                ++ lhs2tex tm ++ ")",
            "                                         ~>  (" ++ lhs2tex t2' ++ ", e_"
                ++ show exn2 ++ "," ++ lhs2tex c1 ++ "," ++ lhs2tex kenv2 ++ ")",
            "            X  =   e_" ++ show exn1 ++ ",kenv_1,fev env",
            "               ~>  " ++ lhs2tex (map ExnVar ([exn1] ++ map fst kenv1 ++ fev env)),
            "            chi'_2  =   solve (kenv_1 ++ " ++ lhs2tex [(exn1,EXN)]
                ++ " ++ kenv) C_1 X e_" ++ show exn2,
            "                    ~>  solve " ++ lhs2tex (kenv1 ++ [(exn1,EXN)] ++ kenv)
                ++ " " ++ lhs2tex c1 ++ " " ++ lhs2tex (map ExnVar v)
                ++ " e_" ++ show exn2,
            "                    ~>  " ++ lhs2tex exn2',
            "            ty'     =   " ++ lhs2tex t',
            "            e_" ++ show e ++ " be fresh",
            "       in   (" ++ lhs2tex t' ++ ", e_" ++ show e ++ ", [], "
                ++ lhs2tex [(e,EXN)] ++ ")"
          ] ["ty'_1", "exn_1", "kenv_1"
            ,"ty'_2", "exn_2", "C_1", "kenv_2"
            , "exn'_2"
            , "x_" ++ show x
            ]

         return (t', e, [], [(e,EXN)])

reconstruct env kenv (App e1 e2)
    = do (t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         (ExnArr t2' (ExnVar exn2') t' exn', kenv') <- instantiate t1
         let subst = [(exn2', ExnVar exn2)] <.> match [] t2 t2'
         e <- fresh
         let c = [substExn' subst exn' :<: e, ExnVar exn1 :<: e] ++ c1 ++ c2

         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             ((" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ "))",
            "    =  let  (ty_1, e_1, C_1, kenv_1)  =   reconstruct env kenv ("
                ++ lhs2tex e1 ++ ")",
            "                                      ~>  (" ++ lhs2tex t1 ++ ", e_"
                ++ show exn1 ++ "," ++ lhs2tex c1 ++ "," ++ lhs2tex kenv1 ++ ")",
            "            (ty_2, e_2, C_2, kenv_2)  =   reconstruct env kenv ("
                ++ lhs2tex e2 ++ ")",
            "                                      ~>  (" ++ lhs2tex t2 ++ ", e_"
                ++ show exn2 ++ "," ++ lhs2tex c2 ++ "," ++ lhs2tex kenv2 ++ ")",
            "            (ExnArr ty'_2 e'_2 ty' e', kenv')  <- instantiate ty_1",
            "                                                        ~> ("
                ++ lhs2tex (ExnArr t2' (ExnVar exn2') t' exn') ++ ", "
                ++ lhs2tex kenv' ++ ")",
            "            theta  =   " ++ lhs2tex [(exn2', ExnVar exn2)]
                ++ " <.> match [] " ++ lhs2tex t2 ++ " " ++ lhs2tex t2',
            "                   ~>  " ++ lhs2tex subst,
            "            e_" ++ show e ++ " be fresh",
            "            C = " ++ lhs2tex [substExn' subst exn' :<: e, ExnVar exn1 :<: e]
                ++ " ++ C_1 ++ C_2",
            "       in   (ApplySubst " ++ lhs2tex subst ++ " " ++ lhs2tex t' ++ ", "
                ++ "e_" ++ show e ++ ", C, "
                ++ "[(e, kindOf (kenv_1 ++ kenv) (ExnVar exn1))] ++ kenv' ++ kenv_2 ++ kenv_1)",
            "                   ~>  (" ++ lhs2tex (substExnTy' subst  t') ++ ", "
                ++ "e_" ++ show e ++ ", " ++ lhs2tex c ++ ", "
                ++ lhs2tex ([(e, kindOf (kenv1 ++ kenv) (ExnVar exn1))]
                    ++ kenv' ++ kenv2 ++ kenv1)
                ++ ")"
            ] ["ty_1", "e_1", "C_1", "kenv_1", "ty_2", "e_2", "C_2", "kenv_2"
              ,"kenv'"]

         return (substExnTy' subst  t', e, c
                ,[(e, kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv' ++ kenv2 ++ kenv1)

reconstruct env kenv (Con b)
    = do e <- fresh
    
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             " ++ show b,
            "    =  let  e_" ++ show e ++ " be fresh",
            "       in   (ExnBool, e_" ++ show e ++ ", EmptySet, "
                ++ lhs2tex [(e,EXN)] ++ ")"
          ] ["e_" ++ show e]
    
         return (ExnBool, e, [], [(e,EXN)])

reconstruct env kenv (Crash lbl ty)
    = do (ty', ExnVar exn1, kenv1) <- C.complete [] ty

         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             bottom_" ++ lbl ++ " : " ++ lhs2tex ty,
            "    =  let  (ty, e, kenv_1) = complete [] (" ++ lhs2tex ty ++ ")"
                ++ " ~> (" ++ lhs2tex ty' ++ ", e_" ++ show exn1 ++ ", "
                ++ lhs2tex kenv1 ++ ")",
            "       in   (ty, e, Set (Set " ++ lbl ++ " :<: e), kenv_1) ~> ("
                ++ lhs2tex ty' ++ ", e_" ++ show exn1 ++ ", Set (Set " ++ lbl
                ++ " :<: e_" ++ show exn1 ++ "), " ++ lhs2tex kenv1 ++ ")"
          ] ["bottom_" ++ lbl]

         return (ty', exn1, [ExnCon lbl :<: exn1], kenv1)

reconstruct env kenv (Seq e1 e2)
    = do (t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         e <- fresh
         
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Seq ((" ++ lhs2tex e1 ++ ")) ((" ++ lhs2tex e2 ++ ")))",
            "    =  let  (ty_1, e_1, C_1, kenv_1)  =   reconstruct env kenv ("
                ++ lhs2tex e1 ++ ")",
            "                                        ~>  (" ++ lhs2tex t1 ++ ", e_"
                ++ show exn1 ++ "," ++ lhs2tex c1 ++ "," ++ lhs2tex kenv1 ++ ")",
            "            (ty_2, e_2, C_2, kenv_2)  =   reconstruct env kenv ("
                ++ lhs2tex e2 ++ ")",
            "                                        ~>  (" ++ lhs2tex t2 ++ ", e_"
                ++ show exn2 ++ "," ++ lhs2tex c2 ++ "," ++ lhs2tex kenv2 ++ ")",
            "            e_" ++ show e ++ " be fresh",
            "       in   ~> (" ++ lhs2tex t2 ++ ", e_" ++ show e ++ ", "
                ++ lhs2tex [ExnVar exn1 :<: e, ExnVar exn2 :<: e] ++ " ++ C_1 ++ C_2, "
                ++ lhs2tex ([(e,kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv2 ++ kenv1)
                ++ ")"
            ] ["ty_1", "exn_1", "C_1", "kenv_1", "ty_2", "exn_2", "C_2", "kenv_2"]
                  
         return (t2, e, [ExnVar exn1 :<: e, ExnVar exn2 :<: e] ++ c1 ++ c2
                ,[(e,kindOf (kenv1 ++ kenv) (ExnVar exn1))] ++ kenv2 ++ kenv1)

reconstruct env kenv (Fix e1)   -- FIXME: unknown to be sound (see notes)
    = do (t1, exn1, c1, kenv1) <- reconstruct env kenv e1
         (ExnArr t' (ExnVar exn') t'' exn'', kenv') <- instantiate t1
         let subst1 = match [] t'' t'
         let subst2 = [(exn', substExn' subst1 exn'')]
         e <- fresh
         let c = [substExn' (subst2 <.> subst1) exn'' :<: e] ++ c1

         debug [ -- FIXME
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Fix (" ++ lhs2tex e1 ++ "))",
            "    =  let  (ty_1, e_1, C_1, kenv_1)  =   reconstruct env kenv ("
                ++ lhs2tex e1 ++ ")",
            "                                      ~>  (" ++ lhs2tex t1 ++ ", e_"
                ++ show exn1 ++ "," ++ lhs2tex c1 ++ "," ++ lhs2tex kenv1 ++ ")",
            "            (ExnArr ty' e' ty'' e'', kenv')  <-  instantiate ty_1",
            "                                             ~>  ("
                ++ lhs2tex (ExnArr t' (ExnVar exn') t'' exn'') ++ ", "
                ++ lhs2tex kenv' ++ ")",
            "            theta_1  =   match [] " ++ lhs2tex t'' ++ " " ++ lhs2tex t',
            "                     ~>  " ++ lhs2tex subst1,
            "            theta_2  =   [(exn', substExn' subst1 exn'')]",
            "                     ~>  " ++ lhs2tex [(exn', substExn' subst1 exn'')],
            "            e_" ++ show e ++ " be fresh",
            "            C = " ++ lhs2tex [substExn' (subst2 <.> subst1) exn'' :<: e]
                ++ " ++ C_1",
            "       in   (ApplySubst ((theta_2 <.> theta_1)) ty'), e_" ++ show e
                ++ ", C, [(e_" ++ show e ++ ",EXN)] ++ kenv' ++ kenv_1)",
            "            ~> (ApplySubst (" ++ lhs2tex (subst2 <.> subst1) ++ ") ("
                ++ lhs2tex t' ++ "), e_" ++ show e ++ "," ++ lhs2tex c ++ ","
                ++ lhs2tex ([(e,EXN)] ++ kenv' ++ kenv1) ++ ")",
            "            ~> (" ++ lhs2tex (substExnTy' (subst2 <.> subst1) t')
                ++ ", e_" ++ show e ++ "," ++ lhs2tex c ++ ","
                ++ lhs2tex ([(e,EXN)] ++ kenv' ++ kenv1) ++ ")"
            ] ["theta_1", "theta_2"]

         return (substExnTy' (subst2 <.> subst1) t', e, c
                ,[(e,EXN)] ++ kenv' ++ kenv1)

reconstruct env kenv (Nil ty)
    = do (ty', ExnVar exn1, kenv1) <- C.complete [] ty
         exn2 <- fresh
         
         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Nil (" ++ lhs2tex ty ++ "))",
            "    =  let  (ty, e, kenv_1) = complete [] (" ++ lhs2tex ty ++ ")"
                ++ " ~> (" ++ lhs2tex ty' ++ ", e_" ++ show exn1 ++ ", "
                ++ lhs2tex kenv1 ++ ")",
            "            e_" ++ show exn2 ++ " be fresh",
            "       in   (" ++ lhs2tex (ExnList ty' (ExnVar exn1)) ++ ", e_"
                ++ show exn2 ++ ", EmptySet, " ++ lhs2tex ([(exn2, EXN)] ++ kenv1) ++ ")"
          ] ["exn_1", "kenv_1", "e_" ++ show exn2]

         -- FIXME: not completely sure about the kind of exn2 (should be ∅)
         return (ExnList ty' (ExnVar exn1), exn2, [], [(exn2, EXN)] ++ kenv1)

reconstruct env kenv (Cons e1 e2)
    = do (t1              , exn1, c1, kenv1) <- reconstruct env kenv e1
         (ExnList t2 exn2', exn2, c2, kenv2) <- reconstruct env kenv e2
         let t = join t1 t2
         ex1 <- fresh
         ex2 <- fresh

         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Cons (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2 ++ "))",
            "    =  let  (ty_1,               e_1, C_1, kenv_1)  =   reconstruct env kenv ("
                ++ lhs2tex e1 ++ ")",
            "                                                    ~>  ("
                ++ lhs2tex t1 ++ ", e_" ++ show exn1 ++ "," ++ lhs2tex c1 ++ ","
                ++ lhs2tex kenv1 ++ ")",
            "            (ExnList ty_2 e'_2,  e_2, C_2, kenv_2)  =   reconstruct env kenv ("
                ++ lhs2tex e2 ++ ")",
            "                                                    ~>  ("
                ++ lhs2tex (ExnList t2 exn2') ++ ", e_" ++ show exn2 ++ ","
                ++ lhs2tex c2 ++ "," ++ lhs2tex kenv2 ++ ")",
            "            ty = join " ++ lhs2tex t1 ++ " " ++ lhs2tex t2
                ++ " ~> " ++ lhs2tex t,
            "            e_" ++ show ex1 ++ " be fresh",
            "            e_" ++ show ex2 ++ " be fresh",
            "       in   (ExnList " ++ lhs2tex t ++ " (ExnVar " ++ show ex1
                ++ "), e_" ++ show ex2
                ++ ", [ExnVar " ++ show exn1 ++ " :<: e_" ++ show ex1 ++ ","
                ++ "" ++ lhs2tex exn2' ++ " :<: e_" ++ show ex1 ++ ","
                ++ "ExnVar " ++ show exn2 ++ " :<: e_" ++ show ex2 ++ "] ++ "
                ++ lhs2tex c1 ++ " ++ " ++ lhs2tex c2 ++ ","
                ++ lhs2tex ([(ex1, kindOf (kenv1 ++ kenv) (ExnVar exn1))
                            ,(ex2, kindOf (kenv2 ++ kenv) (ExnVar exn2))]
                            ++ kenv2 ++ kenv1)
                ++ ")"
          ] ["ty_1", "ty_2", "e_1", "e_2", "C_1", "C_2", "kenv_1", "kenv_2"]

         -- FIXME: not completely sure about the kind of ex1 and ex2 (should be ∅)
         return (ExnList t (ExnVar ex1), ex2
            ,[ExnVar exn1 :<: ex1, exn2' :<: ex1, ExnVar exn2 :<: ex2] ++ c1 ++ c2
            ,[(ex1, kindOf (kenv1 ++ kenv) (ExnVar exn1))
             ,(ex2, kindOf (kenv2 ++ kenv) (ExnVar exn2))] ++ kenv2 ++ kenv1)

reconstruct env kenv (Case e1 e2 x1 x2 e3)
    = do (ExnList t1 exn1', exn1, c1, kenv1) <- reconstruct env kenv e1
         (t2, exn2, c2, kenv2) <- reconstruct env kenv e2
         let env' = (x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env
         (t3, exn3, c3, kenv3) <- reconstruct env' (kenv1 ++ kenv) e3
         let t = join t2 t3
         exn <- fresh
         let c = [ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn]
                    ++ c1 ++ c2 ++ c3

         debug [
            "reconstruct  env@" ++ lhs2tex env,
            "             kenv@" ++ lhs2tex kenv,
            "             (Case (" ++ lhs2tex e1 ++ ") (" ++ lhs2tex e2
                ++ ") (x_" ++ show x1 ++ ") (x_" ++ show x2 ++ ") (" ++ lhs2tex e3 ++ "))",
            "    =  let  (ExnList ty_1 e'_1,  e_1, C_1, kenv_1)  =   reconstruct env kenv ("
                ++ lhs2tex e1 ++ ")",
            "                                                    ~>  ("
                ++ lhs2tex (ExnList t1 exn1') ++ ", e_" ++ show exn1 ++ ","
                ++ lhs2tex c1 ++ "," ++ lhs2tex kenv1 ++ ")",
            "            (ty_2,               e_2, C_2, kenv_2)  =   reconstruct env kenv ("
                ++ lhs2tex e2 ++ ")",
            "                                                    ~>  ("
                ++ lhs2tex t2 ++ ", e_" ++ show exn2 ++ "," ++ lhs2tex c2 ++ ","
                ++ lhs2tex kenv2 ++ ")",
            "            (ty_3,               e_3, C_3, kenv_3)  =   reconstruct "
                ++ lhs2tex ((x1, (t1, exn1')) : (x2, (ExnList t1 exn1', ExnVar exn1)) : env) ++ " " ++ lhs2tex (kenv1 ++ kenv) ++ lhs2tex e3,
            "                                                    ~> ("
                ++ lhs2tex t3 ++ ", e_" ++ show exn3 ++ ", " ++lhs2tex c3 ++ ","
                ++ lhs2tex kenv3 ++ ")",
            "            ty  = join ty_2 ty_3 ~> " ++ lhs2tex t,
            "            e_" ++ show exn ++ "  be fresh",
            "            C   = " ++ lhs2tex [ExnVar exn1 :<: exn, ExnVar exn2 :<: exn, ExnVar exn3 :<: exn] ++ " ++ C_1 ++ C_2 ++ C_3",
            "       in   (" ++ lhs2tex t ++ ", e_" ++ show exn ++ "," ++ lhs2tex c
                ++ ", " ++ lhs2tex ([(exn, kindOf (kenv1 ++ kenv) (ExnVar exn1))]
                ++ kenv3 ++ kenv2 ++ kenv1) ++ ")"
            ] ["x_" ++ show x1, "x_" ++ show x2
              ,"ty_3", "e_3", "C_3", "kenv_3"
              ]

         return (t, exn, c
                ,[(exn, kindOf (kenv1 ++ kenv) (ExnVar exn1))]
                    ++ kenv3 ++ kenv2 ++ kenv1)
         
-- * Kind reconstruction

kindOf :: KindEnv -> Exn -> Kind
kindOf kenv (ExnVar e)
    | Just k <- lookup e kenv = k
    | otherwise               = error "kindOf: not in scope"
kindOf kenv _
    = error "kindOf: not a variable"

-- * Instantiation

instantiate :: ExnTy -> FreshLog Log (ExnTy, KindEnv)
instantiate (ExnForall e k t)
    = do e' <- fresh
         (t', kenv) <- instantiate t
         return (substExnTy e e' t', [(e', k)] ++ kenv)
instantiate t
    = do return (t, [])

-- * Join / subtyping

join :: ExnTy -> ExnTy -> ExnTy
join ExnBool ExnBool
    = ExnBool
join (ExnForall x k t) (ExnForall x' k' t')
    | k == k'   = ExnForall x k (join t (substExnTy x' x t'))
    | otherwise = error "join: kind mismatch"
join (ExnList t exn) (ExnList t' exn')
    = ExnList (join t t') (ExnUnion exn exn')
join (ExnArr t1 (ExnVar exn1) t2 exn2) (ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq (error "don't use me") t1 t1', exn1 == exn1'
        -- TODO: are we sure no alpha-renaming is needed?
        = ExnArr t1 (ExnVar exn1) (join t2 t2') (ExnUnion exn2 exn2')
    | otherwise = error $ "join: function space"
join t t'
    = error $ "join: t = " ++ show t ++ "; t' = " ++ show t'

-- * Match (merge, meet)

match :: KindEnv -> ExnTy -> ExnTy -> Subst
match env (ExnBool) (ExnBool)
    = []
match env (ExnForall e k t) (ExnForall e' k' t')
    | k == k'   = match ((e,k) : env) t (substExnTy e' e t')
    | otherwise = error "match: kind mismatch"
-- FIXME: correct definition for lists?
match env (ExnList t exn) (ExnList t' exn')
    = let (e, es) = deapply exn'
       in [(e, reapply env es exn)] <.> match env t t'
match env t@(ExnArr t1 (ExnVar exn1) t2 exn2) t'@(ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq env t1 t1', exn1 == exn1'
        = let (e, es) = deapply exn2'
           in [(e, reapply env es exn2)] <.> match env t2 t2'
    | otherwise = error $ "match: function space (t = "   ++ show t
                          ++ "; t' = "  ++ show t' ++ "; env = " ++ show env
match env t t'
    = error $ "match: t = " ++ show t ++ "; t' = " ++ show t' ++ "; env = " ++ show env
    
-- NOTE: here the fully-appliedness and left-to-rightness comes into play
-- TODO: check this restriction in never violated
-- TODO: encode this restriction into Exn?
deapply :: Exn -> (Name, [Name])
deapply (ExnVar e) = (e, [])
deapply (ExnApp e1 (ExnVar e2))
    = let (e, es) = deapply e1
       in (e, es ++ [e2])           -- TODO: keep this in reverse order?
deapply _ = error "deapply: malformed"

reapply :: KindEnv -> [Name] -> Exn -> Exn
reapply env es exn
    = foldr (\e r -> ExnAbs e (lookup' "reapply" e env) r) exn es
    
-- * Constraint solving

solve :: KindEnv -> [Constr] -> [Name] -> Name -> Exn
solve env cs xs e =
    let dependencies :: M.Map Name [Constr]
        dependencies = foldr f M.empty cs
            where f c@(exn :<: _) d
                    = foldr (\e -> M.insertWith (++) e [c]) d (fevExn exn)
        
        analysis', analysis'', analysis :: M.Map Name Exn
        analysis' = foldr f M.empty cs
            -- FIXME: we need an abstracted Empty depending on the kind...
            where f (_ :<: e) d = M.insert e ExnEmpty d
        analysis'' = foldr f analysis' xs
            where f e d = M.insert e (ExnVar e) d
        analysis = M.insert e ExnEmpty analysis''
        
        f :: Constr -> M.Map Name Exn -> ([Constr], M.Map Name Exn)
        f (exn :<: e) analysis
                -- FIXME: need a whole lot more βη∪-normalization here
                = let exn1 = interpret analysis exn
                      exn2 = mapLookup "exn2" analysis e
                   in -- FIXME: is this environment sufficient? the call to solve
                      --        in reconstruct suggests perhaps not!
                      if isIncludedIn env exn1 exn2
                      then ( [], analysis )
                      else ( M.findWithDefault [] e dependencies
                           -- FIXME: should the above lookup ever be allowed to fail?
                           --        (it does!)
                           , M.insert e (exnNormalize (ExnUnion exn1 exn2)) analysis )
     in mapLookup "solve result" (worklist f cs analysis) e

-- TODO: move to LambdaUnion
isIncludedIn :: KindEnv -> Exn -> Exn -> Bool
isIncludedIn env exn1 exn2 = exnEq env (ExnUnion exn1 exn2) (exn2)

-- TODO: move to LambdaUnion?
interpret :: M.Map Name Exn -> Exn -> Exn
interpret env (ExnEmpty)
    = ExnEmpty
interpret env (ExnUnion e1 e2)
    = ExnUnion (interpret env e1) (interpret env e2)
interpret env (ExnCon lbl)
    = ExnCon lbl
interpret env (ExnVar e)
    -- FIXME: should this lookup ever fail? it does!
    = M.findWithDefault ExnEmpty e env
interpret env (ExnApp e1 e2)
    = ExnApp (interpret env e1) (interpret env e2)
interpret env (ExnAbs x k e)
    = ExnAbs x k (interpret (M.delete x env) e)

worklist :: (c -> a -> ([c], a)) -> [c] -> a -> a
worklist f [] x     = x
worklist f (c:cs) x = let (cs', x') = f c x in worklist f (cs ++ cs') x'

mapLookup :: (Ord k, Show k, Show a) => String -> M.Map k a -> k -> a
mapLookup msg m k = case M.lookup k m of
    Nothing -> error $ "mapLookup @ " ++ msg ++ ": could not find key '" ++ show k ++ "' in " ++ show m
    Just v  -> v