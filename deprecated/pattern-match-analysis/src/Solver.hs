module Solver where

import Prelude hiding (lookup)
import Data.Map as Map hiding (foldr, map, singleton)
import qualified Data.List as List
import Data.Set (Set, singleton)
import qualified Data.Set as Set

import Language.Haskell.Exts.Annotated

import Common
import PrintType
import Refinement

import Util
import Util.Set

import Abstract.Unit
import Abstract.Bool
import Abstract.Int
import Abstract.List

-- | Dependency analysis

-- * Dependendent constraints for the worklist

data DependencyGraph
    = DependencyGraph { lowerDep :: Map (Name Phi) (Set.Set RefConstr)
                      , upperDep :: Map (Name Phi) (Set.Set RefConstr)
                      }

instance Show DependencyGraph where
    show (DependencyGraph ld ud) = "Lower: {" ++ concatMap showDep (toList ld) ++ "}\n"
                                   ++ "Upper: {" ++ concatMap showDep (toList ud) ++ "}"
                                    where showDep (Ident _ k, v) = "[" ++ k ++ " ~> " ++ showSet v ++ "]"
                                    
type DependencyGraph' = Map (Name Phi) (Set.Set (Name Phi))
                       
dependencyAnalysis :: [RefConstr] -> DependencyGraph
dependencyAnalysis = foldr f (DependencyGraph { lowerDep = Map.empty, upperDep = Map.empty })
    where f :: RefConstr -> DependencyGraph -> DependencyGraph
          f c@(a :<: b) (DependencyGraph { lowerDep = ld, upperDep = ud })
            = DependencyGraph { lowerDep = foldr (\s ldr -> if List.null (getVars b) then ldr else insertWith Set.union s (Set.singleton c) ldr) ld (getVars a)
                              , upperDep = foldr (\s udr -> if List.null (getVars a) then udr else insertWith Set.union s (Set.singleton c) udr) ud (getVars b)
                              }
                              
-- * Full dependency analysis for constraint set partitioning, building on worklist and previous dependency-analysis (see solveRT below for details on the implementation)

dependencyAnalysis' :: [RefConstr] -> DependencyGraph'
dependencyAnalysis' rcs = worklist (g (dependencyAnalysis rcs)) empty rcs
    where
        g :: DependencyGraph -> RefConstr -> DependencyGraph' -> ([RefConstr], DependencyGraph')
        g dep rc dg = let (names, dg') = f rc dg
                          updated      = Set.toList (Set.unions (map checkUpdated (Set.toList names)))
                            where checkUpdated name = if lookup name dg == lookup name dg'
                                                      then Set.empty
                                                      else (findWithDefault Set.empty name (lowerDep dep)) `Set.union` (findWithDefault Set.empty name (upperDep dep))
                       in (updated, dg')
                       
        f :: RefConstr -> DependencyGraph' -> (Set (Name Phi), DependencyGraph')
        f (r1 :<: r2) dg = let rv1    = getVars r1
                               rv1set = Set.fromList rv1
                               rv2    = getVars r2
                               rv2set = Set.fromList rv2
                               dg'    = foldr (\k -> insertWith Set.union k rv2set) dg  rv1
                               dg''   = foldr (\k -> insertWith Set.union k rv1set) dg' rv2
                            in (rv1set `Set.union` rv2set, dg'')
                            
showDG' :: DependencyGraph' -> [String]
showDG' dg = map (\(Ident _ k, v) -> k ++ " ~> " ++ showSet (Set.map (\(Ident _ n) -> n) v)) (toList dg)
                              
-- * Variable extraction
          
getVars :: Refinement -> [Name Phi]
getVars (RefVar  name)    = [name]
getVars (RefList abslist) = getVarsAbsList abslist
getVars _ = []

-- | Generic worklist
worklist :: (a -> b -> ([a], b)) -> b -> [a] -> b
worklist _ r []     = r
worklist f r (x:xs) = let (ys, r') = f x r in worklist f r' (xs ++ ys)


-- | Solver

solveRT :: [RefConstr] -> RefSubst
solveRT rcs = worklist (g (dependencyAnalysis rcs)) empty rcs
    where

        -- * Resolve one constraint (apply f) and check what has been modified
        --   adding relevenant constraints form the dependency graph to the
        --   worklist.
        g :: DependencyGraph -> RefConstr -> RefSubst -> ([RefConstr], RefSubst)
        g dep rc subst = let (names, subst') = f rc subst
                             updated         = Set.toList (Set.unions (map checkUpdated (Set.toList names)))
                                 where checkUpdated name = if lookup name subst == lookup name subst'
                                                           then Set.empty
                                                           else (findWithDefault Set.empty name (lowerDep dep)) `Set.union` (findWithDefault Set.empty name (upperDep dep))
                          in (updated, subst')
                            
        
        -- * Solve a single constraint (resolveContr in thesis)
        f :: RefConstr -> RefSubst -> (Set (Name Phi), RefSubst)
        
        -- Var-var constraints
        f (RefVar name1 :<: RefVar name2) subst
            | Just (l,u) <- Map.lookup name1 subst
                = (singleton name2, insertWith joinRefL name2 (l, u{- should be top -}) subst)
            | otherwise
                = (singleton name2, subst)

        -- Lower-bounds
        f (t@RefTop      :<: RefVar name) subst
            = (singleton name, insertWith joinRefL name (t, RefTop) subst)
        f (l@RefLambda   :<: RefVar name) subst
            = (singleton name, insertWith joinRefL name (l, RefLambda) subst)
        f (u@(RefUnit _) :<: RefVar name) subst
            = (singleton name, insertWith joinRefL name (u, RefUnit topAbsUnit) subst)
        f (b@(RefBool _) :<: RefVar name) subst
            = (singleton name, insertWith joinRefL name (b, RefBool topAbsBool) subst)
        f (i@(RefInt  _) :<: RefVar name) subst
            = (singleton name, insertWith joinRefL name (i, RefInt topAbsInt ) subst)
        f (  (RefList l) :<: RefVar name) subst
            = let subst'           = insertWith joinRefL name (RefList (instAbsList (putSquarePegInRoundHoleL subst) botAbsList l), RefList topAbsList) subst
                  (nameL, subst'') = -- not generic enough yet (as below)...
                                     let (_, RefList l2) = findWithDefault (undefined, RefList topAbsList) name subst'
                                         (l1nil, l1cons) = partitionAbsList l
                                         (l2nil, l2cons) = partitionAbsList l2
                                         l1decons'd      = deconsAbsList l1cons
                                         l2decons'd      = deconsAbsList l2cons
                                      in f (RefList l1decons'd :<: promoteVar (RefList l2decons'd)) subst' -- why promoteVar on right argument only?
               in (singleton name `Set.union` nameL, subst'')

        -- Upper-bounds
        f (RefVar name :<: t@RefTop     ) subst
            = (singleton name, insertWith meetRefU name (RefTop{-botRefTop-}, t) subst)
        f (RefVar name :<: l@RefLambda  ) subst
            = (singleton name, insertWith meetRefU name (RefLambda,           l) subst)
        f (RefVar name :<: b@(RefBool _)) subst
            = (singleton name, insertWith meetRefU name (RefBool botAbsBool, b) subst)
        f (RefVar name :<:   (RefList l)) subst
            = let subst'           = insertWith meetRefU name (RefList botAbsList, RefList (instAbsList (putSquarePegInRoundHoleU subst) topAbsList l)) subst
                  (nameU, subst'') = -- not generic enough yet (promoteVar)...
                                     let (RefList l1, _) = findWithDefault (RefList botAbsList, undefined) name subst'
                                         (l1nil, l1cons) = partitionAbsList l1
                                         (l2nil, l2cons) = partitionAbsList l
                                         l1decons'd      = deconsAbsList l1cons
                                         l2decons'd      = deconsAbsList l2cons
                                      in f (RefList l1decons'd :<: promoteVar (RefList l2decons'd)) subst'
               in (singleton name `Set.union` nameU, subst'')

        -- Catch-all
        f (RefList _ :<: RefList _) subst = (Set.empty, subst) -- why.. why..
        f x                               _     = error ("subst.f: " ++ show x)
        
        -- * Another function that needs to be moved to top-level...
        joinRefL :: (Refinement, Refinement) -> (Refinement, Refinement) -> (Refinement, Refinement)
        joinRefL (RefTop   , _) (RefTop   , u) = (RefTop                    , u)
        joinRefL (RefLambda, _) (RefLambda, u) = (RefLambda                 , u)
        joinRefL (RefUnit a, _) (RefUnit b, u) = (RefUnit (mergeAbsUnit a b), u)
        joinRefL (RefBool a, _) (RefBool b, u) = (RefBool (mergeAbsBool a b), u)
        joinRefL (RefInt  a, _) (RefInt  b, u) = (RefInt  (mergeAbsInt  a b), u)
        joinRefL (RefList a, _) (RefList b, u) = (RefList (mergeAbsList a b), u)
        
        meetRefU :: (Refinement, Refinement) -> (Refinement, Refinement) -> (Refinement, Refinement)
        meetRefU (_, RefTop   ) (l, RefTop   ) = (l, RefTop                   )
        meetRefU (_, RefLambda) (l, RefLambda) = (l, RefLambda                )
        --meetRefU (_, RefUnit a) (l, RefUnit b) = (l, RefUnit (meetAbsUnit a b))
        meetRefU (_, RefBool a) (l, RefBool b) = (l, RefBool (meetAbsBool a b))
        --meetRefU (_, RefInt  a) (l, RefInt  b) = (l, RefInt  (meetAbsInt  a b)) 
        meetRefU (_, RefList a) (l, RefList b) = (l, RefList (meetAbsList a b))

-- | Satisfiability check

isSatisfiable :: RefSubst -> Bool
isSatisfiable = and . map (uncurry refSat . snd) . toList
        
-- | Substitutions

data Variance = Co | Contra
    deriving (Eq, Ord, Show)
    
invert :: Variance -> Variance
invert Co     = Contra
invert Contra = Co

-- * Apply RefVar subsitution to type

asrt :: RefSubst -> Type Phi -> Type Phi
asrt = asrt' Co

asrt' :: Variance -> RefSubst -> Type Phi -> Type Phi
asrt' var subst (TyVar   NoPhi     v)
    = TyVar NoPhi v
asrt' var subst (TyCon (Phi phi) c)
    = TyCon (Phi (asrphi var subst phi)) c
asrt' var subst (TyList (Phi phi) a)
    = TyList (Phi (asrphi var subst phi)) (asrt' var subst a)
asrt' var subst (TyTuple (Phi phi) boxed ts)
    = TyTuple (Phi (asrphi var subst phi)) boxed (map (asrt' var subst) ts)
asrt' var subst (TyFun (Phi phi) a b)
    = TyFun (Phi (asrphi var subst phi)) (asrt' (invert var) subst a) (asrt' var subst b)
asrt' var subst x
    = error ("asrt': " ++ printType x)
    
-- * Helper function for `asrt`

asrphi :: Variance -> RefSubst -> Refinement -> Refinement
asrphi Co     subst r@(RefVar v) = fst (findWithDefault (r, undefined) v subst)
asrphi Contra subst r@(RefVar v) = snd (findWithDefault (undefined, r) v subst)
asrphi _      subst x            = x
        
-- | Input(-dependent) variables

inputVars :: Variance -> Type Phi -> Set (Name Phi)

inputVars _      (TyVar NoPhi     _)
    = Set.empty
inputVars Co     (TyCon _         _)
    = Set.empty
inputVars Contra (TyCon (Phi phi) _)
    = Set.fromList (getVars phi)
inputVars Co     (TyList (Phi phi) tv)
    = inputVars Co tv
inputVars Contra (TyList (Phi phi) tv)
    = Set.fromList (getVars phi) `Set.union` inputVars Contra tv
inputVars Co     (TyTuple (Phi phi) _ tvs)
    = Set.unions (map (inputVars Co) tvs)
inputVars Contra (TyTuple (Phi phi) _ tvs)
    = Set.fromList (getVars phi) `Set.union` (Set.unions (map (inputVars Contra) tvs))
inputVars Co     (TyFun (Phi _) a b)
    = inputVars Contra a `Set.union` inputVars Co b
inputVars Contra (TyFun (Phi _) a b)
    = inputVars Co a `Set.union` inputVars Contra b
inputVars x y
    = error ("inputVars: " ++ show x ++ " | " ++ show y)


dependentVars :: [RefConstr] -> Set (Name Phi) -> Set (Name Phi)
dependentVars rcs init = fix (dv rcs) init -- or use dependencyAnalysis'
    where dv :: [RefConstr] -> Set (Name Phi) -> Set (Name Phi)
          dv []                     vs
            = vs
          dv ((a :<: RefVar b):rcs) vs
            | Set.null (Set.fromList (getVars a) `Set.intersection` vs) = dv rcs vs
            | otherwise                                                 = dv rcs (Set.singleton b `Set.union` vs)
          dv ((RefVar a :<: b):rcs) vs
            | Set.null (Set.fromList (getVars b) `Set.intersection` vs) = dv rcs vs
            | otherwise                                                 = dv rcs (Set.singleton a `Set.union` vs)

-- | Constraint-set partitioning

partitionRCS :: Set (Name Phi) -> [RefConstr] -> ([RefConstr], [RefConstr])
partitionRCS deps = List.partition isDependent
    where isDependent :: RefConstr -> Bool
          isDependent (a :<: b) = not (Set.null (Set.fromList (getVars a) `Set.intersection` deps) && Set.null (Set.fromList (getVars b) `Set.intersection` deps))
          
-- | Pretty printing
        
showSubstRT :: RefSubst -> String
showSubstRT = concatMap (\(x,t) -> prettyPrint x ++ " ↦ " ++ show t ++ "\n") . Map.toList

