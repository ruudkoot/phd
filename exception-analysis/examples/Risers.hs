module Main where

risers :: [Int] -> [[Int]]
risers [ ] = [ ]
risers [x] = [[x]]
risers (x : y : etc) = if x <= y then (x : s) : ss else [x] : (s : ss)
    where (s : ss) = risers (y : etc)
    
main = putStrLn . show $ risers [1,6,3,7,3,6,5]
