{-
    Huet, Gérard (1978). "An algorithm to generate the basis of solutions to
    homogeneous linear Diophantine equations". Inf. Proc. Let. 7(3):144-7.
-}

module Main where

solveLinearDiophantineEquation :: [Integer] -> [Integer] -> [[Integer]]
solveLinearDiophantineEquation as bs
    | all (> 0) as && all (> 0) bs
        = let m = length as
              n = length bs

              max_a = maximum as
              max_b = maximum bs

              d = [ [ lcm a_i b_j `div` a_i | b_j <- bs ] | a_i <- as ]
              e = [ [ lcm a_i b_j `div` b_j | b_j <- bs ] | a_i <- as ]

              es j k xs = [ 1 / fromInteger (e !! (i - 1) !! (j-1))
                          | i <- [1..k]
                          , xs !! (i-1) >= d !! (i-1) !! (j-1)
                          ]

              ys j k xs | null (es j k xs) = fromInteger max_a
                        | otherwise        = minimum (es j k xs)

           in error $ show (d,e)
    | otherwise = error "coefficients must be positive"
