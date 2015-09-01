{-# LANGUAGE ScopedTypeVariables #-}

-- FIXME: Cons (ListShape var) ~> Cons (AbsList var)
-- FIXME: Move ListVar into AbsList
-- FIXME: Reconsider ListVar vs. RefVar?

module Abstract.List {-(AbsList, ListShape, injectList, mergeAbsList, meetAbsList, absCons, substAbsList, instAbsList, headAbsList, getVarsAbsList, subsetAbsList, botAbsList, topAbsList, nonNilAbsList, consAbsList)-} where

import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set hiding (map, null)
import qualified Data.Set as Set

import Language.Haskell.Exts.Pretty

import Util

-- | Widening configuration

maxDepth = 5

-- | List shapes

data ListShape var -- var is needed to avoid mutual recursion between data types
                   -- I'd rather keep in separate modules... (but, "Ord var =>")
    = Nil
    | Cons (ListShape var)
    | Star
--  | Infinite (= Star\Cons)
    | ListVar var
    deriving (Eq, Ord)
    
instance Pretty var => Show (ListShape var) where
    show Nil            = "[]"
    show (Cons ls)      = "_:" ++ show ls
    show Star           = "*"
    show (ListVar name) = prettyPrint name
    
-- | Abstract lists
    
newtype AbsList var
    = AbsList (Set (ListShape var))
    deriving (Eq, Ord)

instance (Ord var, Pretty var) => Show (AbsList var) where
    show l@(AbsList a) | l == topAbsList = "T_List"
                       | otherwise       = "{" ++ concat (intersperse "," (map show (toList a))) ++ "}"

injectList :: [a] -> AbsList var
injectList xs = AbsList (singleton (l2ls xs))

l2ls :: [a] -> ListShape var
l2ls = l2ls' maxDepth
    where
        l2ls' 0 _      = Star
        l2ls' n []     = Nil
        l2ls' n (x:xs) = Cons (l2ls' (n-1) xs)

mergeAbsList :: Ord var => AbsList var -> AbsList var -> AbsList var
mergeAbsList (AbsList a) (AbsList b) = AbsList (a `union` b)

meetAbsList :: Ord var => AbsList var -> AbsList var -> AbsList var
meetAbsList (AbsList a) (AbsList b) = AbsList (a `intersection` b)

absCons :: var -> AbsList var
absCons var = AbsList (singleton (Cons (ListVar var)))

substAbsList :: Ord var => Map var var -> AbsList var -> AbsList var
substAbsList subst (AbsList set) = AbsList (Set.map f set)
    where -- f :: Ord var => ListShape var -> ListShape var
          f Nil            = Nil
          f (Cons l)       = Cons (f l)
          f Star           = Star
          f (ListVar name) = ListVar (Map.findWithDefault name name subst)

instAbsList :: Ord var => Map var (AbsList var) -> AbsList var -> AbsList var -> AbsList var
instAbsList subst dflt (AbsList set) = AbsList (Set.unions (map f (toList set)))
    where -- f :: Ord var => ListShape var -> Set (ListShape var)
          f Nil            = Set.singleton Nil
          f (Cons l)       = let AbsList lss = consAbsList $ instAbsList subst dflt (AbsList (Set.singleton  l)) in lss
          f Star           = Set.singleton Star
          f (ListVar name) | Just (AbsList x) <- Map.lookup name subst = x
                           | otherwise                                 = let AbsList dflt' = dflt in dflt'
          
--headAbsList :: AbsList var -> 
headAbsList (AbsList a) = head . toList $ a

getVarsAbsList :: AbsList var -> [var]
getVarsAbsList (AbsList set) = concatMap getVarsAbsList' (toList set)

getVarsAbsList' :: ListShape var -> [var]
getVarsAbsList' Nil         = []
getVarsAbsList' (Cons lv)   = getVarsAbsList' lv
getVarsAbsList' (ListVar v) = [v]
getVarsAbsList' Star        = []

subsetAbsList :: Ord var => AbsList var -> AbsList var -> Bool
subsetAbsList (AbsList a) (AbsList b) = a `isSubsetOf` b

botAbsList :: AbsList var
botAbsList = AbsList Set.empty

topAbsList :: (Eq var, Ord var) => AbsList var
topAbsList = fix (\s -> s `mergeAbsList` consAbsList s) (injectList [])

nonNilAbsList :: (Eq var, Ord var) => AbsList var
nonNilAbsList = fix (\s -> s `mergeAbsList` consAbsList s) (injectList [undefined])

consAbsList :: Ord var => AbsList var -> AbsList var
consAbsList (AbsList ls) = AbsList (Set.map cons ls)
    where
        cons l = depthLimit (Cons l)
        depthLimit l = depthLimit' maxDepth l
            where
                depthLimit' 0 _         = Star
                depthLimit' n Nil       = Nil
                depthLimit' n (Cons ls) = Cons (depthLimit' (n-1) ls)
                depthLimit' n Star      = Star
                depthLimit' n (ListVar name) = ListVar name   -- shouldn't those be gone here?
                
-- | Evil hackish stuff
                
partitionAbsList :: Ord var => AbsList var -> (AbsList var, AbsList var)
partitionAbsList (AbsList ls) = let (ls1,ls2) = Set.partition (== Nil) ls
                                 in (AbsList ls1, AbsList ls2)

deconsAbsList :: (Ord var, Pretty var) => AbsList var -> AbsList var
deconsAbsList (AbsList ls) = AbsList ((Set.map deconsListShape) ls)
    where deconsListShape (Cons l) = l
          deconsListShape x = error ("deconsAbsShape: " ++ show ls)
    
isVarAbsList :: AbsList var -> Maybe var
isVarAbsList (AbsList l) | [ListVar name] <- Set.toAscList l = Just name
                         | otherwise                         = Nothing
