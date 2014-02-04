{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Main where

import Control.Monad.State hiding (join)

import qualified Data.Map   as M
import           Data.Map   (Map, (!))
import           Data.Maybe (fromJust)
import qualified Data.Set   as S
import           Data.Set   (Set)

data a :+: b
    = L { unL :: a }
    | R { unR :: b }
    deriving (Eq, Ord, Show)

data Name
    = Name String
    | AnnName Int
    | EffName Int
    deriving (Eq, Ord)
    
instance Show Name where
    show (AnnName n) = "β" ++ show n
    show (EffName n) = "δ" ++ show n

type Lbl = Int

-- | Examples

main = undefined

exId =
    Abs () 1 (Name "x") TyBool (
        Var () (Name "x")
    )
       
exConst =
    Abs () 1 (Name "x") TyBool (
        Abs () 2 (Name "y") TyBool (
            Var () (Name "x")
        )
    )
    
exConst' =
    Abs () 1 (Name "x") TyBool (
        Abs () 2 (Name "y") TyBool (
            Var () (Name "y")
        )
    )
    
exApply =
    Abs () 1 (Name "f") (TyBool :-> TyBool) (
        Abs () 2 (Name "x") TyBool (
            App () 3 (Var () (Name "f")) (Var () (Name "x"))
        )
    )

ex1 = Abs () 7 (Name "f") (TyBool :-> TyBool) (
          If () 6 (
              App () 2 (Var () (Name "f")) (Con () 1 False)
          ) (
              App () 4 (Var () (Name "f")) (Con () 3 True)
          ) (
              Con () 5 False
          )
      )

-- | Underlying type system

-- * Types

data Ty
    = TyVar Name
    | TyBool
    | Ty :-> Ty 
    deriving (Eq, Show)
    
-- * Terms (Expressions)

data Tm a
    = Var a Name
    | Con a Lbl Bool
    | Abs a Lbl Name Ty (Tm a)
    | App a Lbl (Tm a) (Tm a)
    | Fix a Lbl (Tm a)
    | If  a Lbl (Tm a) (Tm a) (Tm a)
    deriving (Eq, Show)

-- * Type inference (underlying types)

type Env a = Map Name a
type Env' a = [(Name, a)]

extend :: Env a -> Name -> a -> Env a
extend env x y = M.insert x y env

class FV t where
    fv :: t -> Set Name
    bv :: t -> Set Name
    
instance FV Ann where
    fv (AnnVar beta)        = S.singleton beta
    fv (AnnUnit    )        = S.empty
    fv (AnnCon lbl )        = S.empty
    fv (AnnAbs beta s psi)  = S.delete beta (fv psi)
    fv (AnnApp psi1 psi2)   = S.union (fv psi1) (fv psi2)
    fv (AnnUnion psi1 psi2) = S.union (fv psi1) (fv psi2)
    
    bv (AnnVar beta)        = S.empty
    bv (AnnUnit    )        = S.empty
    bv (AnnCon lbl )        = S.empty
    bv (AnnAbs beta s psi)  = S.insert beta (bv psi)
    bv (AnnApp   psi1 psi2) = S.union (bv psi1) (bv psi2)
    bv (AnnUnion psi1 psi2) = S.union (bv psi1) (bv psi2)

instance FV Eff where
    fv (EffVar delta)        = S.singleton delta
    fv (EffUnit)             = S.empty
    fv (EffCon (lbl,psi))    = fv psi
    fv (EffAbs chi s phi)    = S.delete chi (fv phi)
    fv (EffAppAnn phi psi)   = S.union (fv phi) (fv psi)
    fv (EffAppEff phi1 phi2) = S.union (fv phi1) (fv phi2)
    fv (EffUnion phi1 phi2)  = S.union (fv phi1) (fv phi2)

    bv (EffVar delta)        = S.empty
    bv (EffUnit)             = S.empty
    bv (EffCon (lbl,psi))    = bv psi
    bv (EffAbs chi s phi)    = S.insert chi (bv phi)
    bv (EffAppAnn phi psi)   = S.union (bv phi) (bv psi)
    bv (EffAppEff phi1 phi2) = S.union (bv phi1) (bv phi2)
    bv (EffUnion phi1 phi2)  = S.union (bv phi1) (bv phi2)

instance (FV a, FV b) => FV (a :+: b) where
    fv (L x) = fv x
    fv (R y) = fv y
    
    bv (L x) = bv x
    bv (R y) = bv y    

type Subst a = Map Name a

idSubst :: Subst a
idSubst = M.empty

singletonSubst :: Name -> a -> Subst a
singletonSubst x y = M.singleton x y

class Substitute t e where
    ($@) :: Subst t -> e -> e

instance Substitute Ty Ty where
    subst $@ (TyVar a  ) = M.findWithDefault (TyVar a) a subst
    subst $@ (TyBool   ) = TyBool
    subst $@ (t1 :-> t2) = (subst $@ t1) :-> (subst $@ t2)

instance Substitute Ty (Env Ty) where
    subst $@ env = M.map (subst $@) env
    
checkCapture :: FV a => Name -> Subst a -> b -> b
checkCapture name subst k
    = if S.member name (S.unions (map fv (M.elems subst))) then
          error "checkCapture: substitution may cause variable capture"
      else if S.member name (S.unions (map bv (M.elems subst))) then
          error "checkCapture: substitution may cause shadowing"
      else
          k

instance Substitute Ann Ann where
    subst $@ (AnnVar beta)
        = M.findWithDefault (AnnVar beta) beta subst
    subst $@ (AnnUnit)
        = AnnUnit
    subst $@ (AnnCon lbl)
        = AnnCon lbl
    subst $@ (AnnAbs beta s psi)
        = checkCapture beta subst (AnnAbs beta s (M.delete beta subst $@ psi))
    subst $@ (AnnApp psi1 psi2)
        = AnnApp (subst $@ psi1) (subst $@ psi2)
    subst $@ (AnnUnion psi1 psi2)
        = AnnUnion (subst $@ psi1) (subst $@ psi2)
        
instance Substitute (Ann :+: Eff) Ann where
    subst $@ (AnnVar beta)
        = unL (M.findWithDefault (L (AnnVar beta)) beta subst)
    subst $@ (AnnUnit)
        = AnnUnit
    subst $@ (AnnCon lbl)
        = AnnCon lbl
    subst $@ (AnnAbs beta s psi)
        = checkCapture beta subst (AnnAbs beta s (M.delete beta subst $@ psi))
    subst $@ (AnnApp psi1 psi2)
        = AnnApp (subst $@ psi1) (subst $@ psi2)
    subst $@ (AnnUnion psi1 psi2)
        = AnnUnion (subst $@ psi1) (subst $@ psi2)

instance Substitute Ann Eff where
    subst $@ (EffVar delta)
        = EffVar delta
    subst $@ (EffUnit)
        = EffUnit
    subst $@ (EffCon (lbl, psi))
        = EffCon (lbl, subst $@ psi)
    subst $@ (EffAbs chi s phi)
        = checkCapture chi subst (EffAbs chi s (M.delete chi subst $@ phi))
    subst $@ (EffAppAnn phi psi)
        = EffAppAnn (subst $@ phi) (subst $@ psi)
    subst $@ (EffAppEff phi1 phi2)
        = EffAppEff (subst $@ phi1) (subst $@ phi2)
    subst $@ (EffUnion phi1 phi2)
        = EffUnion (subst $@ phi1) (subst $@ phi2)

instance Substitute Eff Eff where
    subst $@ (EffVar delta)
        = M.findWithDefault (EffVar delta) delta subst
    subst $@ (EffUnit)
        = EffUnit
    subst $@ (EffCon (lbl, psi))
        = EffCon (lbl, psi)
    subst $@ (EffAbs chi s phi)
        = checkCapture chi subst (EffAbs chi s (M.delete chi subst $@ phi))
    subst $@ (EffAppAnn phi psi)
        = EffAppAnn (subst $@ phi) psi
    subst $@ (EffAppEff phi1 phi2)
        = EffAppEff (subst $@ phi1) (subst $@ phi2)
    subst $@ (EffUnion phi1 phi2)
        = EffUnion (subst $@ phi1) (subst $@ phi2)

instance Substitute (Ann :+: Eff) Eff where
    subst $@ (EffVar delta)
        = unR (M.findWithDefault (R (EffVar delta)) delta subst)
    subst $@ (EffUnit)
        = EffUnit
    subst $@ (EffCon (lbl, psi))
        = EffCon (lbl, subst $@ psi)
    subst $@ (EffAbs chi s phi)
        = checkCapture chi subst (EffAbs chi s (M.delete chi subst $@ phi))
    subst $@ (EffAppAnn phi psi)
        = EffAppAnn (subst $@ phi) (subst $@ psi)
    subst $@ (EffAppEff phi1 phi2)
        = EffAppEff (subst $@ phi1) (subst $@ phi2)
    subst $@ (EffUnion phi1 phi2)
        = EffUnion (subst $@ phi1) (subst $@ phi2)

instance Substitute (Ann :+: Eff) (Ann :+: Eff) where
    subst $@ (L x) = L (subst $@ x)
    subst $@ (R y) = R (subst $@ y)

instance Substitute (Ann :+: Eff) AnnTy where
    s $@ (AnnTyBool)
        = AnnTyBool
    s $@ (AnnTyArr annty1 psi1 phi annty2 psi2)
        = AnnTyArr (s $@ annty1) (s $@ psi1) (s $@ phi) (s $@ annty2) (s $@ psi2)
    s $@ (Forall a sort annty)
        = checkCapture a s (Forall a sort (s $@ annty))

($.) :: (Substitute t t, Show t) => Subst t -> Subst t -> Subst t
s2 $. s1 = (s2 $$ s1) $+ s2
    where ($$), ($+) :: (Substitute t t, Show t) => Subst t -> Subst t -> Subst t
          subst $$ tv
            = M.map (subst $@) tv
          tv1 $+ tv2
            = M.unionWith overlapError tv1 tv2
                where overlapError a b
                        = error $ "($+): overlapping substitutions:"
                                  ++ " a = "    ++ show a
                                  ++ ", b = "   ++ show b
                                  ++ ", tv1 = " ++ show tv1
                                  ++ ", tv2 = " ++ show tv2

-- The middle Ty in the resulting type is superfluous, as it is already
-- the the top-level annotation of the resulting Tm.
infer :: Env Ty -> Tm () -> Maybe (Subst Ty, Ty, Tm Ty)
infer env (Var _ x)
    = do let ty = env ! x
         return (idSubst, ty, Var ty x)
infer env (Con _ lbl c)
    = do return (idSubst, TyBool, Con TyBool lbl c)
infer env (Abs _ lbl x ty1 tm)
    = do (s, ty2, tm') <- infer (extend env x ty1) tm
         let ty = ty1 :-> ty2
         return (s, ty, Abs ty lbl x ty1 tm')
infer env (App _ lbl tm1 tm2)
    = do (s1, ty1 :-> ty2, tm1') <- infer        env  tm1
         (s2, ty3        , tm2') <- infer (s1 $@ env) tm2
         s3 <- unify ty1 ty3
         let ty = (s3 $. s2) $@ ty2
         return (s3 $. s2 $. s1, ty, App ty lbl tm1' tm2')
infer env (Fix _ lbl tm)
    = do (s1, ty :-> ty', tm') <- infer env tm
         s2 <- unify ty ty'
         let ty'' = s2 $@ ty'
         return (s2 $. s1, ty'', Fix ty'' lbl tm')
infer env (If _ lbl tm1 tm2 tm3)
    = do (s1, ty1, tm1') <- infer env tm1
         (s2, ty2, tm2') <- infer env tm2
         (s3, ty3, tm3') <- infer env tm3
         s4 <- unify ty1 TyBool
         s5 <- unify ty2 ty3
         let ty = ty3
         return (s5 $. s4 $. s3 $. s2 $. s1, ty, If ty lbl tm1' tm2' tm3')
         
unify :: Ty -> Ty -> Maybe (Subst Ty)
unify TyBool TyBool
    = return idSubst
unify (ty1 :-> ty2) (ty3 :-> ty4)
    = do s1 <- unify        ty1         ty3
         s2 <- unify (s1 $@ ty2) (s1 $@ ty4)
         return (s2 $. s1)
unify _ _
    = do fail "could not unify"

-- | Flow analysis

data Sort
    = ANN
    | EFF
    | Sort :=> Sort
    deriving (Eq, Show)

data AnnTy
    = AnnTyBool
    | AnnTyArr AnnTy Ann Eff AnnTy Ann
    | Forall Name Sort AnnTy
    deriving (Eq, Show) -- FIXME: need semantic equality

data Constr
    = A Ann Name
    | E Eff Name
    deriving Show
    
type AnnVar = Name
type EffVar = Name
    
data Ann
    = AnnVar AnnVar
    | AnnUnit
    | AnnCon Lbl
    | AnnAbs Name Sort Ann
    | AnnApp Ann Ann
    | AnnUnion Ann Ann
    deriving (Eq, Show) -- FIXME: need semantic equality
    
data Eff
    = EffVar EffVar
    | EffUnit
    | EffCon (Lbl, Ann)
    | EffAbs Name Sort Eff  -- FIXME: split in EffAbsAnn and EffAbsEff?
    | EffAppAnn Eff Ann
    | EffAppEff Eff Eff
    | EffUnion Eff Eff
    deriving (Eq, Show) -- FIXME: need semantic equality

type AnnM a = State Int a

freshAnn, freshEff :: AnnM Name
freshAnn = do n <- get
              modify (+1)
              return (AnnName n)
freshEff = do n <- get
              modify (+1)
              return (EffName n)

reconstruct :: Env (AnnTy, Ann) -> Tm Ty -> AnnM (AnnTy, AnnVar, EffVar, [Constr])
reconstruct env (Var ty x)
    = do let (annty, psi) = env ! x
         beta  <- freshAnn
         delta <- freshEff
         let constrs = [psi `A` beta]
         return (annty, beta, delta, constrs)
reconstruct env (Con TyBool lbl c)
    = do beta  <- freshAnn
         delta <- freshEff
         let constrs = [AnnCon lbl `A` beta]
         return (AnnTyBool, beta, delta, constrs)
reconstruct env (Abs (ty1 :-> ty2) lbl x _ty1 tm1) -- ty1 == _ty1
    = do (annty1, sorts) <- complete ty1 []
         beta1 <- freshAnn
         let env' = extend env x (annty1, AnnVar beta1)
         (annty2, beta2, delta0, constrs1) <- reconstruct env' tm1
         let xs = S.singleton beta1 `S.union` S.fromList (map fst sorts) `S.union` ffv env
         let (psi2, phi0) = solve constrs1 xs beta2 delta0
         let annty = quantify ((beta1,ANN) : sorts)
                              (AnnTyArr annty1 (AnnVar beta1) phi0 annty2 psi2)
         beta  <- freshAnn
         delta <- freshEff
         let constrs = [AnnCon lbl `A` beta]
         return (annty, beta, delta, constrs)
reconstruct env (If ty lbl tm1 tm2 tm3)
    = do (AnnTyBool, beta1, delta1, constrs1) <- reconstruct env tm1
         (annty2   , beta2, delta2, constrs2) <- reconstruct env tm2
         (annty3   , beta3, delta3, constrs3) <- reconstruct env tm3
         let annty = join annty2 annty3
         beta  <- freshAnn
         delta <- freshEff
         let constrs = [ EffVar delta1              `E` delta
                       , EffCon (lbl, AnnVar beta1) `E` delta
                       , EffVar delta2              `E` delta
                       , EffVar delta3              `E` delta
                       , AnnVar beta2               `A` beta
                       , AnnVar beta3               `A` beta
                       ] ++ constrs1 ++ constrs2 ++ constrs3
         return (annty, beta, delta, constrs)
reconstruct env (App ty lbl tm1 tm2)
    = do (annty1, beta1, delta1, constrs1) <- reconstruct env tm1
         (annty2, beta2, delta2, constrs2) <- reconstruct env tm2
         (AnnTyArr annty2' (AnnVar beta2') phi0' annty' psi') <- instantiate annty1
         let subst = singletonSubst beta2' (L (AnnVar beta2)) $. match [] annty2 annty2'
         beta  <- freshAnn
         delta <- freshEff
         let constrs = [ EffVar delta1              `E` delta
                       , EffVar delta2              `E` delta
                       , EffCon (lbl, AnnVar beta1) `E` delta
                       , subst $@ phi0'             `E` delta
                       , subst $@ psi'              `A` beta
                       ] ++ constrs1 ++ constrs2
         return (subst $@ annty', beta, delta, constrs)

class FFV a where
    ffv :: a -> Set Name
    
instance (FFV a, FFV b) => FFV (a, b) where
    ffv (x, y) = ffv x `S.union` ffv y

instance FFV a => FFV (Env a) where
    ffv = S.unions . map ffv . M.elems 

instance FFV AnnTy where
    ffv AnnTyBool
        = S.empty
    ffv (AnnTyArr annty1 psi1 phi annty2 psi2)
        = S.unions ([ffv annty1, ffv psi1, ffv phi, ffv annty2, ffv psi2])
    ffv (Forall chi _s annty)
        = S.delete chi (ffv annty)

instance FFV Ann where
    ffv (AnnVar beta       ) = S.singleton beta
    ffv (AnnUnit           ) = S.empty
    ffv (AnnCon _          ) = S.empty
    ffv (AnnAbs beta _s psi) = S.delete beta (ffv psi)
    ffv (AnnApp   psi1 psi2) = ffv psi1 `S.union` ffv psi2
    ffv (AnnUnion psi1 psi2) = ffv psi1 `S.union` ffv psi2

instance FFV Eff where
    ffv (EffVar delta       ) = S.singleton delta
    ffv (EffUnit            ) = S.empty
    ffv (EffCon _           ) = S.empty
    ffv (EffAbs delta _s phi) = S.delete delta (ffv phi)
    ffv (EffAppAnn phi  psi ) = ffv phi  `S.union` ffv psi
    ffv (EffAppEff phi1 phi2) = ffv phi1 `S.union` ffv phi2
    ffv (EffUnion  phi1 phi2) = ffv phi1 `S.union` ffv phi2

-- * Figure 8: Completion algorithm

(+>) :: [a] -> [a] -> [a]
(+>) = flip (++)

infixl 5 +>

complete :: Ty -> Env' Sort -> AnnM (AnnTy, Env' Sort)
complete TyBool _
    = do return (AnnTyBool, [])
complete (ty1 :-> ty2) xsi@(unzip -> (xi,si))
    = do (annty1, xsj@(unzip -> (xj,sj))) <- complete ty1 []
         beta1 <- freshAnn
         (annty2, xsk@(unzip -> (xk,sk))) <- complete ty2 (xsi +> [(beta1,ANN)] +> xsj)
         let (unzip -> (bi',si')) = annvars xsi
         let (unzip -> (bj',sj')) = annvars xsj
         beta0  <- freshAnn
         delta0 <- freshEff
         let beta0APP  = applicateA beta0  (bi' +> [beta1]       +> bj')
         let delta0APP = applicateE delta0 (xsi +> [(beta1,ANN)] +> xsj)
         return ( quantify ([(beta1,ANN)] +> xsj)
                           (AnnTyArr annty1 (AnnVar beta1) delta0APP annty2 beta0APP)
                , [ (beta0,  arrify (si' +> [ANN] +> sj' +> [ANN]))
                  , (delta0, arrify (si  +> [ANN] +> sj  +> [EFF]))
                  ] +> xsk
                )

varCategory :: Sort -> Sort
varCategory ANN         = ANN
varCategory EFF         = EFF
varCategory (s1 :=> s2) = varCategory s2

annvars :: Env' Sort -> Env' Sort
annvars []                                      = []
annvars ((beta , s@(varCategory -> ANN)) : env) = (beta, s) : annvars env
annvars (_                               : env) =             annvars env

applicateA :: AnnVar -> [Name] -> Ann
applicateA = foldr (\beta r -> AnnApp r (AnnVar beta)) . AnnVar

applicateE :: EffVar -> Env' Sort -> Eff
applicateE = foldr (\(chi, s) r -> case varCategory s of
    { ANN -> EffAppAnn r (AnnVar chi)
    ; EFF -> EffAppEff r (EffVar chi)
    }) . EffVar

quantify :: Env' Sort -> AnnTy -> AnnTy
quantify sorts annty = foldl (\r (x,s) -> Forall x s r) annty sorts

arrify :: [Sort] -> Sort
arrify = foldl1 (flip (:=>))

-- * Figure 9: Join algorithm

-- FIXME: types should be considered equivalent up to alpha-renaming!

join :: AnnTy -> AnnTy -> AnnTy
join AnnTyBool AnnTyBool
    = AnnTyBool
join (AnnTyArr annty1 beta1 phi1 annty12 psi12)
     (AnnTyArr annty1' beta1' phi2 annty22 psi22)
       | annty1 == annty1', beta1 == beta1'
         = AnnTyArr annty1 beta1 (phi1 `EffUnion` phi2) (join annty12 annty22) (psi12 `AnnUnion` psi22)
       | otherwise = error "join: annty1 and beta1 do not match"
join (Forall chi s annty11) (Forall chi' s' annty21)
       | chi == chi', s == s'
         = Forall chi s (join annty11 annty21)
       | otherwise = error "join: chi and s do not match"
join _ _
    = error "join: fail"

-- * Figure 10: Instantiation algorithm

instantiate :: AnnTy -> AnnM AnnTy
instantiate (Forall chi s annty1)
    = do chi' <- case varCategory s of {ANN -> freshAnn; EFF -> freshEff}
         annty1' <- instantiate annty1
         let subst = singletonSubst chi ((case varCategory s of {ANN -> L . AnnVar; EFF -> R . EffVar}) chi')
         return (subst $@ annty1')
instantiate annty1
    = do return annty1

-- * Figure 11: Matching algorithm

match :: Env' Sort ->  AnnTy -> AnnTy -> Subst (Ann :+: Eff)
match env AnnTyBool AnnTyBool
    = idSubst
match env (AnnTyArr annty1  beta1  phi        annty2  psi2)
          (AnnTyArr annty1' beta1' delta0chis annty2' beta0betas)
    | annty1 == annty1', beta1 == beta1'
        = let (delta0, chis) = deapplyEff delta0chis
              (beta0, betas) = deapplyAnn beta0betas
              subst1 = singletonSubst beta0  (L (abstractifyAnn env betas psi2))
              subst2 = singletonSubst delta0 (R (abstractifyEff env chis  phi ))
           in subst2 $. subst1 $. match env annty2 annty2'
    | otherwise = error "match: annty1 and beta1 do not match"
match env (Forall chi s annty1) (Forall chi' s' annty1')
    | chi == chi', s == s'
        = let env' = (chi,s) : env in match env' annty1 annty1'
    | otherwise = error "match: chi and s do not match"
match _ _ _
    = error "match: fail"

deapplyAnn :: Ann -> (AnnVar, [Name])
deapplyAnn (AnnVar beta0)
    = (beta0, [])
deapplyAnn (AnnApp ann (AnnVar beta))
    = let (beta0, chis) = deapplyAnn ann in (beta0, beta : chis)

deapplyEff :: Eff -> (EffVar, [Name])
deapplyEff (EffVar delta0)
    = (delta0, [])
deapplyEff (EffAppAnn eff (AnnVar beta))
    = let (delta0, chis) = deapplyEff eff in (delta0, beta : chis)
deapplyEff (EffAppEff eff (EffVar delta))
    = let (delta0, chis) = deapplyEff eff in (delta0, delta : chis)

abstractifyAnn :: Env' Sort -> [Name] -> Ann -> Ann
abstractifyAnn env chis psi
    = foldr (\chi -> AnnAbs chi (fromJust $ lookup chi env)) psi chis

abstractifyEff :: Env' Sort -> [Name] -> Eff -> Eff
abstractifyEff env chis phi
    = foldr (\chi -> EffAbs chi (fromJust $ lookup chi env)) phi chis

-- * Figure 12: Worklist algorithm for constraint solving

l :: Constr -> Ann :+: Eff
l (A ann _) = L ann
l (E eff _) = R eff

r :: Constr -> Name
r (A _ x) = x
r (E _ x) = x

ffl :: Constr -> Set Name
ffl (A ann _) = ffv ann
ffl (E eff _) = ffv eff

solve :: [Constr] -> Set Name -> AnnVar -> EffVar -> (Ann, Eff)
solve cs xs beta delta =
    -- initialization
    let worklist     = cs
        analysis     = M.fromList
                (map f cs ++ map g (S.toList xs) ++ [(beta,L AnnUnit),(delta,R EffUnit)])
            where f (A ann x) = (x, L AnnUnit)
                  f (E eff x) = (x, R EffUnit)
                  g x@(AnnName _) = (x, L (AnnVar x))
                  g x@(EffName _) = (x, R (EffVar x))
        dependencies = foldr f initDep cs
            where initDep = M.fromList (map (,[]) allChis)
                    where allChis = concatMap (S.toList . ffl) cs
                  f c depm = S.fold (\x' -> M.insertWith (++) x' [c]) depm (ffl c)
    -- iteration
        result = work f analysis worklist
            where f an c =
                    let xi  = l c
                        chi = r c
                        
                        an' = M.insertWith unionAE chi (interp an xi) an
                        cs' = dependencies ! chi

                     in if (interp an xi) `notSub` (an ! chi) then
                            (an', cs')
                        else
                            (an, [])
    -- finalization
     in (unL (result ! beta), unR (result ! delta))

-- * Call-by-name evaluator for the type-level lambda calculus
interp :: Map Name (Ann :+: Eff) -> Ann :+: Eff -> Ann :+: Eff
interp env (L (AnnVar beta))
    = let L psi = env ! beta
       in if psi /= AnnVar beta then
              interp env (L psi)
          else
              L (AnnVar beta)
interp env (R (EffVar delta))
    = let R phi = env ! delta
       in if phi /= EffVar delta then
              interp env (R phi)
          else
              R (EffVar delta)
interp env (L AnnUnit)
    = L AnnUnit
interp env (R EffUnit)
    = R EffUnit
interp env (L (AnnCon lbl))
    = L (AnnCon lbl)
interp env (R (EffCon (lbl, psi)))
    = let (L psi') = interp env (L psi)
       in R (EffCon (lbl, psi'))
interp env (L (AnnAbs beta s psi))
    = L (AnnAbs beta s psi)
interp env (R (EffAbs delta s phi))
    = R (EffAbs delta s phi)
interp env (L (AnnApp psi1 psi2))
    = let (L (AnnAbs beta s psi1')) = interp env (L psi1)
       in interp env (L (singletonSubst beta psi2 $@ psi1'))
interp env (R (EffAppAnn phi psi))
    = let (R (EffAbs delta s phi')) = interp env (R phi)
       in interp env (R (singletonSubst delta psi $@ phi'))
interp env (R (EffAppEff phi1 phi2))
    = let (R (EffAbs delta s phi1')) = interp env (R phi1)
       in interp env (R (singletonSubst delta phi2 $@ phi1'))
interp env (L (AnnUnion psi1 psi2))
    = let (L psi1') = interp env (L psi1)
          (L psi2') = interp env (L psi2)
       in L (AnnUnion psi1' psi2')
interp env (R (EffUnion phi1 phi2))
    = let (R phi1') = interp env (R phi1)
          (R phi2') = interp env (R phi2)
       in R (EffUnion phi1' phi2')

interpEnv = M.fromList [(AnnName 1,L $ AnnVar (AnnName 1)),(AnnName 2,L $ AnnVar (AnnName 2)),(AnnName 3,L $ AnnVar (AnnName 3))]
       
ann1, ann2 :: Ann
ann1 = AnnApp (AnnAbs (AnnName 2) ANN (AnnVar (AnnName 3))) (AnnVar (AnnName 1))
ann2 = AnnApp (AnnAbs (AnnName 2) ANN (AnnVar (AnnName 2))) (AnnVar (AnnName 1))

notSub :: Ann :+: Eff -> Ann :+: Eff -> Bool
notSub = undefined

unionAE :: Ann :+: Eff -> Ann :+: Eff -> Ann :+: Eff
unionAE (L ann1) (L ann2) = L (AnnUnion ann1 ann2)
unionAE (R eff1) (R eff2) = R (EffUnion eff1 eff2)

work :: (a -> b -> (a, [b])) -> a -> [b] -> a
work f a []     = a
work f a (c:cs) = let (a', cs') = f a c in work f a' (cs' ++ cs)
