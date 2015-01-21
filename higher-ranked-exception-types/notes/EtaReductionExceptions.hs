module Main where

apply1 :: (Bool -> Bool) -> (Bool -> Bool)
apply1 = \f -> f

apply2 :: (Bool -> Bool) -> (Bool -> Bool)
apply2 = \f -> \x -> f x
