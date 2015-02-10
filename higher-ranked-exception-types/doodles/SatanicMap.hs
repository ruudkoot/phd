satanicMap :: (Bool -> Bool) -> [Bool] -> [Bool]
satanicMap f xs =
    case xs of
        [] -> []
        (y:ys) -> (case satanicMap f ys of { [] -> True; (z:zs) -> z }) `seq` f y : satanicMap f ys

test1 = length $        map not (map (error . show) [1..10]) -- 10
test2 = length $ satanicMap not (map (error . show) [1..10]) -- Exception "10"
