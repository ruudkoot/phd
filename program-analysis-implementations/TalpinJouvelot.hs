{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module TalpinJouvelot where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

-- | Syntax

type Ident    = String

data Expr
    = Var Ident
    | App Expr  Expr
    | Abs Ident Expr
    | Let Ident Expr Expr
    | New Expr
    | Get Expr
    | Set Expr  Expr
    deriving (Eq, Show)

-- | Dynamic Semantics

data Value
    = Unit
    | Ref     Ident
    | Closure Ident Expr Env
    deriving (Eq, Show)

type Env   = M.Map Ident Value
type Store = M.Map Ident Value

eval :: Store -> Env -> Expr -> State [Ident] (Value, Store)
eval s env (Var x)      | Just v <- M.lookup x env = return (v, s)
                        | otherwise = error "unbound variable"
eval s env (Abs x e)    = return (Closure x e env, s)
eval s env (Let x e e') = do (v, s') <- eval s env e
                             (v', s'') <- eval s' (M.insert x v env) e'
                             return (v', s'')
eval s env (App e e')   = do (Closure x e'' env', s') <- eval s env e
                             (v', s'') <- eval s' env e'
                             (v'', s''') <- eval s'' (M.insert x v' env') e''
                             return (v'', s''')
eval s env (New e)      = do l <- fresh
                             (v, s') <- eval s env e
                             return (Ref l, M.insert l v s')
eval s env (Get e)      = do (Ref l, s') <- eval s env e
                             let Just v = M.lookup l s'
                             return (v, s')
eval s env (Set e e')   = do (Ref l, s') <- eval s env e
                             (v, s'') <- eval s' env e'
                             return (Unit, M.insert l v s'')
                             
eval' e = fst (runState (eval M.empty M.empty e) freshIdents)

-- | Static Semantics

data Type
    = TyUnit
    | TyVar Ident
    | TyRef Region Type
    | TyFun Type   Effect Type
    deriving (Eq, Ord)
    
data TypeScheme
    = TypeScheme [Ident] [Ident] [Ident] Type Constrs
    deriving (Eq, Show)

type TyEnv = M.Map Ident TypeScheme

data Region
    = RegCon Ident
    | RegVar Ident
    deriving (Eq, Ord)
    
data EffectElem
    = Init  Region Type
    | Read  Region Type
    | Write Region Type
    | EffVar Ident
    deriving (Eq, Ord)
    
type Effect = S.Set EffectElem

data Constr
    = Effect :>: Effect
    deriving (Eq, Ord, Show)

type Constrs = S.Set Constr

-- * Effects 

getEffVar eff
    | S.size eff == 1, EffVar e <- S.findMin eff = e
    | otherwise = error "not an effect variable"

-- * Free variables

-- FIXME: Can we make this into a 2-parameter type class, to avoid having
--        multiple functions, as in Substitutable?
class FreeVars t where
    ftv :: t -> S.Set Ident
    frv :: t -> S.Set Ident
    fev :: t -> S.Set Ident
    fr  :: t -> S.Set Ident
    
instance FreeVars Type where
    ftv TyUnit         = S.empty
    ftv (TyVar a)      = S.singleton a
    ftv (TyRef r t)    = ftv r `S.union` ftv t
    ftv (TyFun t s t') = ftv t `S.union` ftv t' `S.union` ftv s
    
    frv TyUnit         = S.empty
    frv (TyVar a)      = S.empty
    frv (TyRef r t)    = frv r `S.union` frv t
    frv (TyFun t s t') = frv t `S.union` frv t' `S.union` frv s
    
    fev TyUnit         = S.empty
    fev (TyVar a)      = S.empty
    fev (TyRef r t)    = fev r `S.union` fev t
    fev (TyFun t s t') = fev t `S.union` fev t' `S.union` fev s
    
    fr  TyUnit         = S.empty
    fr  (TyVar a)      = S.empty
    fr  (TyRef r t)    = fr r `S.union` fr t
    fr  (TyFun t s t') = fr t `S.union` fr t' `S.union` fr s

instance FreeVars Region where
    ftv (RegCon r) = S.empty
    ftv (RegVar r) = S.empty
    
    frv (RegCon r) = S.empty
    frv (RegVar r) = S.singleton r
    
    fev (RegCon r) = S.empty
    fev (RegVar r) = S.empty

    fr  (RegCon r) = S.singleton r
    fr  (RegVar r) = S.singleton r
    
instance FreeVars EffectElem where
    ftv (Init  r t) = ftv r `S.union` ftv t
    ftv (Read  r t) = ftv r `S.union` ftv t
    ftv (Write r t) = ftv r `S.union` ftv t
    ftv _           = S.empty

    frv (Init  r t) = frv r `S.union` frv t
    frv (Read  r t) = frv r `S.union` frv t
    frv (Write r t) = frv r `S.union` frv t
    frv _           = S.empty
    
    fev (EffVar  z) = S.singleton z
    fev (Init  r t) = fev r `S.union` fev t
    fev (Read  r t) = fev r `S.union` fev t
    fev (Write r t) = fev r `S.union` fev t
    
    fr  (Init  r t) = fr r `S.union` fr t
    fr  (Read  r t) = fr r `S.union` fr t
    fr  (Write r t) = fr r `S.union` fr t
    fr  _           = S.empty
    
instance FreeVars t => FreeVars (S.Set t) where
    ftv = S.unions . map ftv . S.toList
    frv = S.unions . map frv . S.toList
    fev = S.unions . map fev . S.toList
    fr  = S.unions . map fr  . S.toList

instance FreeVars TyEnv where   
    ftv = S.unions . map ftv . M.elems
    frv = S.unions . map frv . M.elems
    fev = S.unions . map fev . M.elems
    fr  = S.unions . map fr  . M.elems
    
instance FreeVars TypeScheme where -- FIXME: check this
    ftv (TypeScheme tvs rvs evs t k)
        = (ftv t `S.union` ftv k) `S.difference` (S.fromList tvs)
    frv (TypeScheme tvs rvs evs t k)
        = (frv t `S.union` frv k) `S.difference` (S.fromList rvs)
    fev (TypeScheme tvs rvs evs t k)
        = (fev t `S.union` fev k) `S.difference` (S.fromList evs)
    fr  (TypeScheme tvs rvs evs t k)
        = (fr  t `S.union` fr  k) `S.difference` (S.fromList rvs)
        
instance FreeVars Constr where
    ftv (e :>: e') = ftv e `S.union` ftv e'
    frv (e :>: e') = frv e `S.union` frv e'
    fev (e :>: e') = fev e `S.union` fev e'
    fr  (e :>: e') = fr  e `S.union` fr  e'
    
-- * Substitutions

data Subst = Subst
    { tv_ :: M.Map Ident Type
    , rv_ :: M.Map Ident Region    -- Always a RegVar?
    , ev_ :: M.Map Ident Effect    -- Always an EffVar?
    }
    
idSubst = Subst M.empty M.empty M.empty

infixr 9 $.

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 rv1 ev1) (Subst tv2 rv2 ev2)
            = Subst (M.unionWith (error "type variables not distinct")   tv1 tv2)
                    (M.unionWith (error "region variables not distinct") rv1 rv2)
                    (M.unionWith (error "effect variables not distinct") ev1 ev2)
        
($\) :: Subst -> [Ident] -> Subst -- FIXME: inefficient
(Subst { tv_ = tv, rv_ = rv, ev_ = ev }) $\ vs
    = Subst { tv_ = prune tv, rv_ = prune rv, ev_ = prune ev }
        where prune m = foldr M.delete m vs
    
class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv rv ev) = Subst (M.map (subst $@) tv)
                                      (M.map (subst $@) rv)
                                      (M.map (subst $@) ev)
    
instance Substitute Type where
    subst $@ (TyVar a)      | Just t <- M.lookup a (tv_ subst) = t
    subst $@ (TyRef r t)    = TyRef (subst $@ r) (subst $@ t)
    subst $@ (TyFun t s t') = TyFun (subst $@ t) (subst $@ s) (subst $@ t')
    _     $@ x              = x

instance Substitute Region where
    subst $@ (RegVar v) | Just r <- M.lookup v (rv_ subst) = r
    _     $@ x          = x

instance Substitute Effect where
    subst $@ eff = flattenSetOfSets (S.map substElem eff)
        where substElem (EffVar s)  | Just eff <- M.lookup s (ev_ subst) = eff
              substElem (Init  r t) = S.singleton (Init  (subst $@ r) (subst $@ t))
              substElem (Read  r t) = S.singleton (Read  (subst $@ r) (subst $@ t))
              substElem (Write r t) = S.singleton (Write (subst $@ r) (subst $@ t))
              substElem x           = S.singleton x
    
instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env

instance Substitute TypeScheme where
    subst $@ (TypeScheme tvs rvs evs t k)
        = let subst' = subst $\ (tvs ++ rvs ++ evs)
           in TypeScheme tvs rvs evs (subst' $@ t) (subst' $@ k)
           
instance Substitute Constr where
    subst $@ (z :>: s) = (subst $@ z) :>: (subst $@ s)
    
instance Substitute Constrs where
    subst $@ k = S.map (subst $@) k

-- * Instantiation

inst :: TypeScheme -> State [Ident] (Type, Constrs)
inst (TypeScheme tvs rvs evs t k)
    = do tvs' <- freshSubst tvs TyVar
         rvs' <- freshSubst rvs RegVar
         evs' <- freshSubst evs (S.singleton . EffVar)
         let subst = Subst tvs' rvs' evs'
         return (subst $@ t, subst $@ k)
    
-- * Generalization
    
gen :: Constrs -> TyEnv -> Effect -> Type -> (TypeScheme, Constrs)
gen k env eff t = let tvs = inEnvAndEff ftv
                      rvs = inEnvAndEff frv
                      evs = inEnvAndEff fev
                      (kv, kv') = S.partition p k
                      p :: Constr -> Bool
                      p (z :>: s) = (getEffVar z) `elem` evs
                   in (TypeScheme tvs rvs evs t kv, kv')
    where
        inEnvAndEff :: (forall t. FreeVars t => t -> S.Set Ident) -> [Ident]
        inEnvAndEff fv = S.toList (fv (bar k $@ t) `S.difference` (fv (bar k $@ env) `S.union` fv (bar k $@ eff)))
                 
-- * Inference algorithm

infer :: TyEnv -> Constrs -> Expr -> State [Ident] (Subst, Type, Effect, Constrs)
infer env k e = do (subst, t, eff, k') <- infer' env k e
                   return (subst, t, observe (bar k' $@ (subst $@ bar' env)) (bar k' $@ t) (bar k' $@ eff), k')
                 
infer' :: TyEnv -> Constrs -> Expr -> State [Ident] (Subst, Type, Effect, Constrs)
infer' env k (Var x)
    | Just sigma <- M.lookup x env
        = do (t', k') <- inst sigma
             return (idSubst, t', S.empty, k `S.union` k')
    | otherwise = error "unbound variable"
infer' env k (Abs x e)
    = do _a <- fresh
         _z <- fresh
         let a = TypeScheme [] [] [] (TyVar _a) S.empty
         let z = S.singleton (EffVar _z)
         (subst, t, eff, k') <- infer (M.insert x a env) k e
         return (subst, TyFun (subst $@ (TyVar _a)) z t, S.empty, k' `S.union` S.singleton (z :>: eff))
infer' env k (App e1 e2)
    = do (subst1, t1, eff1, k1) <- infer env k e1
         (subst2, t2, eff2, k2) <- infer (subst1 $@ env) k1 e2
         _a <- fresh
         _z <- fresh
         let a = TyVar _a
         let z = S.singleton (EffVar _z)
         let subst3 = unify k2 (subst2 $@ t1) (TyFun t2 z a)
         let k' = subst3 $@ k2
         let subst = subst3 $. subst2 $. subst1
         return (subst, subst3 $@ a, subst3 $@ (subst2 $@ eff1 `S.union` eff2 `S.union` z), k')
infer' env k (Let x e1 e2)
    = do (subst1, t1, eff1, k1) <- infer env k e1
         let (scheme, k1'') = gen k1 (subst1 $@ env) eff1 t1
         (subst2, t, eff2, k') <- infer (M.insert x scheme (subst1 $@ env)) k1'' e2
         return (subst2 $. subst1, t, subst2 $@ eff1 `S.union` eff2, k')
infer' env k (New e)
    = do infer' env k (App (Var "New") e)
infer' env k (Get e)
    = do infer' env k (App (Var "Get") e)
infer' env k (Set e e')
    = do infer' env k (App (App (Var "Set") e) e')

-- * Unification

unify :: Constrs -> Type -> Type -> Subst
unify k TyUnit TyUnit
    = idSubst
unify k (TyVar a) (TyVar a')
    = Subst (M.singleton a (TyVar a')) M.empty M.empty
unify k (TyVar a) t
    | a `S.member` ftv (bar k $@ t) = error "occurs check"
    | otherwise                     = Subst (M.singleton a t) M.empty M.empty
unify k t (TyVar a)
    | a `S.member` ftv (bar k $@ t) = error "occurs check"
    | otherwise                     = Subst (M.singleton a t) M.empty M.empty
unify k (TyRef (RegVar r) t) (TyRef r' t')
    = let subst = Subst M.empty (M.singleton r r') M.empty
       in unify (subst $@ k) (subst $@ t) (subst $@ t') $. subst
unify k (TyFun ti z tf) (TyFun ti' z' tf') -- FIXME: check if z, z' are really singleton
    = let subst_i = unify k ti ti'
          subst_f = unify (subst_i $@ k) (subst_i $@ tf) (subst_i $@ tf')
          subst   = Subst M.empty M.empty (M.singleton (getEffVar (subst_f $@ subst_i $@ z)) (subst_f $@ subst_i $@ z')) $. subst_f $. subst_i
       in if wf (subst $@ k) then subst else error "not well-formed"
unify _ _ _
    = error "cannot unify"
    
-- * Principal models

bar :: Constrs -> Subst
bar = S.foldr (\(z :>: s) r -> Subst M.empty M.empty (M.singleton (getEffVar z) (r $@ (z `S.union` s))) $. r) idSubst

bar' :: TyEnv -> TyEnv
bar' = M.map (\(TypeScheme tvs rvs evs t k) -> TypeScheme tvs rvs evs (bar k $@ t) S.empty)
    
-- * Well-formedness

rng :: Effect -> S.Set (Region, Type)
rng = flattenSetOfSets . S.map rng'
    where rng' (EffVar _ ) = S.empty -- error "variable in range"
          rng' (Init  r t) = S.singleton (r, t)
          rng' (Read  r t) = S.singleton (r, t)
          rng' (Write r t) = S.singleton (r, t)

wf :: Constrs -> Bool
wf = and . S.toList . mapWithComplement f
    where f (z :>: s) k' = and (S.toList (S.map (\(_, t) -> (getEffVar z) `S.notMember` fev t) (rng (bar k' $@ s))))

-- * Observable effects

observe :: TyEnv -> Type -> Effect -> Effect
observe env t eff
    = S.filter f eff
        where f (EffVar           z ) = z `S.member` (fev env `S.union` fev t)
              f (Init  (RegVar r) t') = r `S.member` (fr  env `S.union` fr  t)
              f (Read  (RegVar r) t') = r `S.member` (fr  env `S.union` fr  t)
              f (Write (RegVar r) t') = r `S.member` (fr  env `S.union` fr  t)
              f _                     = False
              
-- * Initial environment

-- FIXME: Types given in [TJ94] seem to be incorrect!

env0 :: TyEnv
env0 = M.fromList [ ("Set", TypeScheme ["a"] ["r"] ["z", "z'"]
                                       (TyFun (TyRef r a) z (TyFun a z' TyUnit))
                                       (S.singleton (z' :>: S.singleton (Write r a))))
                  , ("Get", TypeScheme ["a"] ["r"] ["z"]
                                       (TyFun (TyRef r a) z a)
                                       (S.singleton (z :>: S.singleton (Read r a))))
                  , ("New", TypeScheme ["a"] ["r"] ["z"]
                                       (TyFun a z (TyRef r a))
                                       (S.singleton (z :>: S.singleton (Init r a))))
                  ]
    where a  = TyVar  "a"
          r  = RegVar "r"
          z  = S.singleton (EffVar "z")
          z' = S.singleton (EffVar "z'")

-- | Helper functions

-- * Fresh identifiers

fresh :: State [a] a
fresh = do (x:xs) <- get
           put xs
           return x
           
freshIdents = map (('?':) . show) [1..]
           
freshSubst :: [Ident] -> (Ident -> t) -> State [Ident] (M.Map Ident t)
freshSubst vs inj
    = do vs' <- replicateM (length vs) fresh
         return (M.fromList (zipWith (\v v' -> (v, inj v')) vs vs'))

-- * Missing

mapWithComplement :: (Ord a, Ord b) => (a -> S.Set a -> b) -> S.Set a -> S.Set b
mapWithComplement f s = S.map g s
    where g x = let (l, r) = S.split x s in f x (l `S.union` r)
    
flattenSetOfSets :: Ord a => S.Set (S.Set a) -> S.Set a
flattenSetOfSets = S.unions . S.toList

-- | Pretty printing

instance Show Type where
    show TyUnit         = "unit"
    show (TyVar a)      = "t" ++ a
    show (TyRef r t)    = "ref_" ++ show r ++ "(" ++ show t ++ ")"
    show (TyFun t s t') = "(" ++ show t ++ " --" ++ showSet s ++ "-> " ++ show t' ++ ")"

instance Show Region where
    show (RegVar r) = "r" ++ r
    show (RegCon r) = "R" ++ r

instance Show EffectElem where
    show (EffVar  z) = "e" ++ z
    show (Init  r t) = "Init(" ++ show r ++ "," ++ show t ++ ")"
    show (Read  r t) = "Read(" ++ show r ++ "," ++ show t ++ ")"
    show (Write r t) = "Write(" ++ show r ++ "," ++ show t ++ ")"
    
showSet :: Show a => S.Set a -> String
showSet x = "{" ++ concat (L.intersperse "," (map show (S.toList x))) ++ "}"

instance Show Subst where
    show (Subst t r e) = "[" ++ concat (L.intersperse ", " (map show_t (M.toList t) ++ map show_r (M.toList r) ++ map show_e (M.toList e))) ++ "]"
        where show_t (k, a) = "t" ++ k ++ " ~> " ++ show a
              show_r (k, a) = "r" ++ k ++ " ~> " ++ show a
              show_e (k, a) = "e" ++ k ++ " ~> " ++ showSet a
              
-- | Main

main = do print (doit id')
          print (doit rid)
          print (doit nop)
          print (doit idid)
          print (doit id1)
          print (doit id2)
          print (doit id3)

doit e = let ((subst, t, eff, k), s) = runState (infer env0 S.empty e) freshIdents
          in if S.null eff then t else error "non-empty effect"

-- * Examples

id'  = Abs "x" (Var "x")
rid  = Abs "x" (Get (New (Var "x")))
nop  = Abs "f" (Abs "x" (Let "g" (Abs "y" (App (Var "f") (Var "x"))) (Var "x")))
idid = Let "id" id' (App (Var "id") (Var "id"))
id1  = Let "x" (App id' id') rid
id2  = Abs "y" (App (App rid id') (Var "y"))
id3  = App (App nop rid) id'
