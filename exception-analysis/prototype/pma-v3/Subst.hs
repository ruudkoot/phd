{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Subst where

import qualified Data.Map      as M
import qualified Data.Map.Util as M
import qualified Data.Set      as S -- for the instance only

import Names

-- | Substitutions

type Subst t = M.Map Name t

idSubst :: Subst t
idSubst = M.empty

class Substitute t e where
    ($@) :: Subst t -> e -> e

($.) :: (Substitute t t, Show t) => Subst t -> Subst t -> Subst t
s2 $. s1 = (s2 $$ s1) $+ s2
    where ($$), ($+) :: (Substitute t t, Show t) => Subst t -> Subst t -> Subst t
          subst $$ tv
            = M.map (subst $@) tv
          tv1 $+ tv2
            = M.unionWith overlapError tv1 tv2
                where overlapError a b
                        = error $ "Types.$+: overlapping substitutions:"
                                  ++ " a = "    ++ show a
                                  ++ ", b = "   ++ show b
                                  ++ ", tv1 = " ++ show tv1
                                  ++ ", tv2 = " ++ show tv2

($\) :: Subst t -> S.Set Name -> Subst t
($\) = M.restrictBySet
                                  
-- * Concrete instances

instance Substitute Name Name where
    subst $@ name
        | Just name' <- M.lookup name subst = name'
        | otherwise                         = name

-- * Generic instances

instance Substitute s () where
    subst $@ () = ()
                                  
instance Substitute s t => Substitute s (Maybe t) where
    subst $@ m = fmap (subst $@) m
    
instance Substitute s t => Substitute s (x, y, t) where
    subst $@ (x, y, z) = (x, y, subst $@ z)
    
instance (Substitute s t, Ord t) => Substitute s (S.Set t) where
    subst $@ x = S.map (subst $@) x
