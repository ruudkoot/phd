module Util where

fixpoint f x
    = let fx = f x in if fx == x then x else fixpoint f fx
