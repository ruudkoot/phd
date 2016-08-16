{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ViewPatterns           #-}

module Unif where

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
