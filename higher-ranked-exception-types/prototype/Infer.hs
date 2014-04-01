module Infer where

-- TODO: reconstruct derivation tree

import           Names
import           Common
import qualified LambdaUnion as LU
import qualified Completion  as C

import qualified Data.Map    as M

-- | Expressions

data Expr
    = Var Name
    | Abs Name Ty Expr
    | App Expr Expr
    -- TODO: Crash Ty
    
instance Show Expr where
    show (Var x    ) = "x" ++ show x
    show (Abs x t e) = "(λx" ++ show x ++ ":" ++ show t ++ "." ++ show e ++ ")"
    show (App e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    
-- | Exception type reconstruction

-- * Environments

type Env = [(Name, (ExnTy, Exn))]

fev :: Env -> [Name]
fev = concatMap (\(_, (ty, exn)) -> fevExnTy ty ++ fevExn exn)

-- * Constraints

data Constr = Exn :<: Name
    deriving Show

-- * Reconstruction

-- TODO: env1, ... are kind environments, rename?
reconstruct :: Env -> KindEnv -> Expr -> Fresh (ExnTy, Name, [Constr])
reconstruct env kenv (Var x)
    = do let Just (t, exn) = lookup x env
         e <- fresh
         return (t, e, [exn :<: e])
reconstruct env kenv (Abs x ty tm)
    = do (t1', exn1, kenv1) <- C.complete [] ty
         exn <- fresh
         let env' = (x, (t1', ExnVar exn)) : env
         (t2', exn2, c1) <- reconstruct env' (kenv1 ++ kenv) tm
         let v = [exn] ++ map fst kenv1 ++ fev env
         -- FIXME: is this the correct environment we are passing here? this
         --        environment contains exactly the variables over which we
         --        do NOT generalize. this would seem to correspond to the
         --        variables that are FREE in c1... which could be okay.
         --
         --        however, we do seem to be missing at least fev env!!!
         let exn2' = solve (kenv1 ++ [(exn,EXN)] ++ kenv) c1 v exn2
         let t' = ExnForall exn EXN (C.forallFromEnv kenv1 (
                    ExnArr t1' (ExnVar exn) t2' exn2'
                  ))
         e <- fresh
         return (t', e, [])
reconstruct env kenv (App e1 e2)
    = do (t1, exn1, c1) <- reconstruct env kenv e1
         (t2, exn2, c2) <- reconstruct env kenv e2
         ExnArr t2' (ExnVar exn2') t' exn' <- instantiate t1
         let subst = [(exn2', ExnVar exn2)] <.> merge [] t2 t2'
         e <- fresh
         let c = c1 ++ c2 ++ [substExn' subst exn' :<: e, ExnVar exn1 :<: e]
         return (substExnTy' subst  t', e, c)

-- * Instantiation

-- TODO: ExnTy -> Fresh (ExnTy, KindEnv)

instantiate :: ExnTy -> Fresh ExnTy
instantiate (ExnForall e k t)
    = do e' <- fresh
         t' <- instantiate t
         return (substExnTy e e' t')
instantiate t
    = do return t
    
-- * Merge / match

merge :: KindEnv -> ExnTy -> ExnTy -> Subst
merge env (ExnForall e k t) (ExnForall e' k' t')
    | k == k'   = merge ((e,k) : env) t (substExnTy e' e t')
    | otherwise = error "merge: kind mismatch"
merge env (ExnBool) (ExnBool)
    = []
merge env (ExnList t (ExnVar exn)) (ExnList t' (ExnVar exn'))
    | exnTyEq env t t', exn == exn' = []
    | otherwise                     = error "merge: lists"
merge env (ExnArr t1 (ExnVar exn1) t2 exn2) (ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq env t1 t1', exn1 == exn1'
        = let (e, es) = deapply exn2'
           in [(e, reapply env es exn2)] <.> merge env t2 t2'
    | otherwise = error "merge: function space"
merge _ _ _
    = error "merge: fail"
    
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
                           , M.insert e (ExnUnion exn1 exn2) analysis )      
                           -- FIXME: need to normalize the expression when updating
                           --        the analysis result above
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
interpret env (ExnVar e)
    = mapLookup "interpret" env e
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
