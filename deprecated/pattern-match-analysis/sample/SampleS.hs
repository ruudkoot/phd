{-# LANGUAGE NoImplicitPrelude #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}

module Test where

data Bool
    = True
    | False

data Either a b
    = Left a
    | Right b
    
-- | rt-unit

-- main = ()

-- | rt-con

-- main = True
-- main = 42

-- | rt-var

-- main = let x = 13 in x 

-- | rt-fun

main = let id = (\x -> x) in id
