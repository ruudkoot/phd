{-------------------------------------------------------------------------------

    STILL TO DO FOR agUnifN:
    * implement Elim properly
      * occur-check?
    * FIXME (e.g. Simplify)
    * Mem-Rec has been "fixed"(?) w.r.t. Boudet et al.

    SANITY CHECKING:
    * of unification results
    
-------------------------------------------------------------------------------}

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif where

import Prelude hiding (log)

import Control.Applicative ((<$>))
import Control.Arrow ((***),(&&&))
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List

import           Data.Function
import           Data.Graph
import           Data.List      ( intersect, minimumBy, nub, partition, sort, sortBy
                                , zip4
                                )
import           Data.Maybe
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Set       hiding (filter, foldr, map, partition, null)
import qualified Data.Set       as Set

import Unif.FirstOrder.Types
import Unif.FirstOrder.Free
import Unif.FirstOrder.AbelianGroups
import Unif.FirstOrder.General
import Unif.HigherOrder.Equational

-- | Higher-order dimension types | ---------------------------------------[ ]--

instance Theory () AG where
    signature Mul  = [(),()] :=> ()
    signature Inv  = [()]    :=> ()
    signature Unit = []      :=> ()
    
    unify          = unify' agUnifN
