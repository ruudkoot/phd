{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Constr where

import qualified Data.Graph      as G
import qualified Data.Graph.Util as G
import qualified Data.List       as L
import qualified Data.List.Util  as L
import qualified Data.Map        as M
import qualified Data.Map.Util   as M
import           Data.Maybe
import qualified Data.Set        as S
import qualified Data.Set.Util   as S
import qualified Data.Tree       as T

import Names
import FTV
import Subst
import Shapes

-- | Subset constraints

type Constr a b = S.Set (Constr' a b)

data Constr' a b
    = Sh      :<# Sh             -- "undecomposed" constraints
    | CC (S.Set b) Name Sh Sh    -- FIXME: "undecomposed" conditionals, i.e. we
                                 -- need to rethink our constraints
    | LHS a b :<: Name           -- decomposed constraints
    deriving (Eq, Ord, Show)
    
data LHS a b
    = V Name
    | C (S.Set a)
    | I (S.Set b) Name (S.Set a) -- FIXME: need to be careful here to maintain
                                 --        monotonicity, B should not grow?
                                 --        (i.e. B should be variable free, or
                                 --         the computation staged, so variables
                                 --         can be substituted away.)
                                 --        on the other hand, propagating a
                                 --        conditional constraint might be sound
                                 --        in out situation (but imprecise)
    deriving (Eq, Ord, Show)
    -- FIXME: - merge V and C using a general Free-purpose data type
    --        - add a bit vector framework-like constraint
    
instance (ConstrElem a, ConstrElem b) => FTV (Constr' a b) where
    ftv (sh1  :<# sh2 )
        = ftv sh1 `S.union` ftv sh2
    ftv (CC _ name sh1 sh2) 
        = name `S.insert` ftv sh1 `S.union` ftv sh2
    ftv (V v1 :<: v2  )
        = S.fromList [v1, v2]
    ftv (C sa :<: name) 
        = name `S.insert` S.unionMap ftv sa
    ftv (I sb v1 sa :<: v2)
        | S.null (ftv sb) = S.fromList [v1, v2] `S.union` ftv sa
        | otherwise       = error "sb not variable free"

instance (Substitute Name a, Substitute Name b, Ord a, Ord b, Show a, Show b)
            => Substitute Name (Constr' a b) where
    subst $@ (sh1 :<# sh2)
        = (subst $@ sh1) :<# (subst $@ sh2)
    subst $@ (CC sa n sh1 sh2)
        = CC (S.map (subst $@) sa) (subst $@ n) (subst $@ sh1) (subst $@ sh2)
            -- FIXME: sa should be variable free
    -- subst $@ (V x  :<: name) = V (subst $@ x)          :<: (subst $@ name)
    subst $@ (C sa :<: name)
        = C (S.map (subst $@) sa) :<: (subst $@ name)
    _ $@ x
        = error $ "subst: " ++ show x
    
class (FTV a, Ord a, Show a) => ConstrElem a where
    injName :: Name -> a
    prjName :: a -> Maybe Name
    prjName' :: a -> Name
    prjName' = fromJust . prjName
    
instance FTV () where
    ftv = error "instance FTV (): ftv"
    
instance ConstrElem () where -- FIXME: needed for (currently unused) Constr Ref ()
    injName = error "instance ConstrElem (): injName"
    prjName = error "instance ConstrElem (): prjName"

-- | Constraint decomposition

decompose :: (ConstrElem a, ConstrElem b) => Constr a b -> Constr a b
decompose = S.unionMap decompose' where
    decompose' :: (ConstrElem a, ConstrElem b) => Constr' a b -> Constr a b

    decompose' c@(_   :<: _  )
        = S.singleton c

    -- "undecomposed" constraints
    decompose' (ShBase n1 :<# ShBase n2)
        = decompose' (V n1 :<: n2)
    decompose' (ShFun sh1 sh2 n1 :<# ShFun sh3 sh4 n2)
        = decompose' (sh3 :<# sh1) `S.union` decompose' (sh2 :<# sh4)
            `S.union` decompose' (V n1 :<: n2)
    decompose' (ShPair sh1 sh2 n1 :<# ShPair sh3 sh4 n2)
        = decompose' (sh1 :<# sh3) `S.union` decompose' (sh2 :<# sh4)
            `S.union` decompose' (V n1 :<: n2)
    decompose' (ShList sh1 n1 :<# ShList sh2 n2)
        = decompose' (sh1 :<# sh2) `S.union` decompose' (V n1 :<: n2)

    -- "undecomposed" implication constraints (composed conditionals)
    decompose' (CC t x (ShBase n1) (ShBase n2))
        = decompose' (I t x (S.singleton (injName n1)) :<: n2)
    decompose' (CC t x (ShFun sh1 sh2 n1) (ShFun sh3 sh4 n2))
        = decompose' (CC t x sh3 sh1) `S.union` decompose' (CC t x sh2 sh4)
            `S.union` decompose' (I t x (S.singleton (injName n1)) :<: n2)
    decompose' (CC t x (ShPair sh1 sh2 n1) (ShPair sh3 sh4 n2))
        = decompose' (CC t x sh1 sh3) `S.union` decompose' (CC t x sh2 sh4)
            `S.union` decompose' (I t x (S.singleton (injName n1)) :<: n2)
    decompose' (CC t x (ShList sh1 n1) (ShList sh2 n2))
        = decompose' (CC t x sh1 sh2)
            `S.union` decompose' (I t x (S.singleton (injName n1)) :<: n2)

    decompose' x
        = error $ "decompose': " ++ show x

-- | Dependency analysis

dependsOn :: (ConstrElem a, ConstrElem b) => Constr' a b -> S.Set Name
dependsOn (V      a  :<: _)
    = S.singleton a
dependsOn (C      as :<: _)
    = ftv as
dependsOn (I bs n as :<: _)
    | S.null (ftv bs) = n `S.insert` ftv as
    | otherwise       = error $ "dependsOn: " ++ "bs should be variable free"

influences :: Constr' a b -> Name -- FIXME: we can generalize this to a set
influences (_ :<: name) = name

buildDependencyMap :: (ConstrElem a, ConstrElem b) =>
                        Constr a b -> M.Map Name (Constr a b)
buildDependencyMap cs
    = S.foldr
        (\c r -> S.foldr
                    (\d r' -> M.insertWith S.union d (S.singleton c) r')
                    r
                    (dependsOn c)
        )
        M.empty
        cs

-- | Constraint solving

-- FIXME: assumes a type with no input variables, or variables bound in the
--        environment

-- FIXME: merge solveRef and solveExn

type Solution a = M.Map Name (S.Set a)

solveRef :: (ConstrElem a, Show a) => Constr a a -> Solution a
solveRef cs
    = L.worklist updateSolution initialSolution (S.toList cs)
        where
            dependencies
                = M.map S.toList (buildDependencyMap cs)

            initialSolution
                = S.foldr (\x r -> M.insert x S.empty r) M.empty (ftv cs)

            updateSolution c s
                = let k        = influences c
                      original = s M.! k
                      updated  = original `S.union` interpretLHS c s s
                   in if original == updated
                      then (s, [])
                      else (M.insert k updated s, M.findWithDefault [] k dependencies)

solveExn :: (ConstrElem a, ConstrElem b, Show a) => Constr a b -> Solution b -> Solution a
solveExn cs sb                        -- it seems the "staged"ness comes out naturally...
    = L.worklist updateSolution initialSolution (S.toList cs)
        where
            dependencies
                = M.map S.toList (buildDependencyMap cs)

            initialSolution
                = S.foldr (\x r -> M.insert x S.empty r) M.empty (ftv cs)

            updateSolution c s
                = let k        = influences c
                      original = s M.! k
                      updated  = original `S.union` interpretLHS c sb s
                   in if original == updated
                      then (s, [])
                      else (M.insert k updated s, M.findWithDefault [] k dependencies)
                        -- FIXME: make sure dependencies is complete instead of fWD?

interpretLHS (lhs :<: _) sb s
    = case lhs of
        V x      -> s M.! x
        C as     -> S.unionMap (interpretElem s) as
        I t x as -> if t `S.isSubsetOf` (M.findWithDefault S.empty x sb) --FIXME: default to empty?
                    then S.unionMap (interpretElem s) as
                    else S.empty
    where
        interpretElem s e
            = case prjName e of
                Just x  -> s M.! x
                Nothing -> S.singleton e
                    
-- | Solution validation

validateSolution :: (ConstrElem a, ConstrElem b) => Constr a b -> Solution b -> Solution a -> Bool
validateSolution cs sb sol
    = if S.all valid cs then True else error "invalid solution"
        where
            valid (V x :<: y)
                = (sol M.! x) `S.isSubsetOf` (sol M.! y)
            valid c@(C _ :<: y)
                = interpretLHS c sb sol `S.isSubsetOf` (sol M.! y)
            valid c@(I bs x _ :<: y)
                = interpretLHS c sb sol `S.isSubsetOf` (sol M.! y)

-- | Constraint graph visualization

graphviz :: (ConstrElem a, ConstrElem b, ConstrElem c, ConstrElem d)
    => Sh -> Constr a b -> Solution a -> Constr c d -> Solution c -> String
graphviz sh cs1 sol1 cs2 sol2
    = "digraph C {\n"
      ++ concatMap nodesV (S.toList (ftv sh `S.union` ftv cs1 `S.union` ftv cs2))
      ++ concatMap (edgesV ""                    ) (S.toList cs1)
      ++ concatMap (edgesV " [color=red]"        ) (S.toList cs2)
      ++ concatMap (nodesC ""                    ) (S.toList cs1)
      ++ concatMap (nodesC ",fillcolor=lightpink") (S.toList cs2)
      ++ concatMap (edgesD ""                    ) (S.toList cs1)
      ++ concatMap (edgesD "[color=red]"         ) (S.toList cs2)
      ++ concatMap (edgesI ""                    ) (S.toList cs1)
      ++ concatMap (edgesI "[color=red]"         ) (S.toList cs2)
      ++ "}"
    where posVars = positiveVariables sh
          negVars = negativeVariables sh
          invVars = posVars `S.intersection` negVars

          showNode :: Name -> String
          showNode n
            = show n
                ++ " = "
                ++ (if n `M.member` sol1 then S.showSet (sol1 M.! n) else "--")
                ++ "/"
                ++ (if n `M.member` sol2 then S.showSet (sol2 M.! n) else "--")
          
          nodesV :: Name -> String
          nodesV name = " \"" ++ showNode name ++ "\" [fontcolor=" ++ pickColor ++ "];\n"
            where pickColor | name `S.member` invVars = "green"
                            | name `S.member` negVars = "red"
                            | name `S.member` posVars = "blue"
                            | otherwise = "black"

          edgesV :: ConstrElem a => String -> Constr' a b -> String
          edgesV postfix (sh1 :<# sh2)
            = " \"" ++ show sh1 ++ "\" -> \"" ++ show sh2 ++ "\" [style=dashed];\n"
                -- FIXME: no postfix here
          edgesV postfix (V v :<: a)
            = " \"" ++ showNode v ++ "\" -> \"" ++ showNode a ++ "\"" ++ postfix ++ ";\n"
          edgesV postfix (C c :<: a)
            | S.size c == 1, Just n <- prjName (head (S.toList c))
                = " \"" ++ showNode n ++ "\" -> \"" ++ showNode a ++ "\"" ++ postfix ++ ";\n"
            | otherwise
                = " \"" ++ show c ++ "\" -> \"" ++ showNode a ++ "\"" ++ postfix ++ ";\n"
          edgesV postfix (I t x c :<: a)
            = "" --FIXME: figure a good way to represent these..

          nodesC :: (ConstrElem a, ConstrElem b) => String -> Constr' a b -> String
          nodesC style c
            = " \"" ++ show c ++ "\" [style=filled" ++ style ++ "];\n"

          edgesD :: (ConstrElem a, ConstrElem b) => String -> Constr' a b -> String
          edgesD postfix c
            = concatMap f (S.toList (dependsOn c))
                where f :: Name -> String
                      f name = " \"" ++ showNode name  ++ "\" -> \""
                               ++ show c ++ "\"" ++ postfix ++ ";\n"

          edgesI postfix c
            = " \"" ++ show c ++ "\" -> \""
              ++ showNode (influences c) ++ "\"" ++ postfix ++ ";\n"
