module Analysis.LambdaUnionNew.Equality (
    semanticallyEqual
) where

import Analysis.LambdaUnionNew.Types
import Analysis.LambdaUnionNew.Reduce

semanticallyEqual :: Env -> Tm -> Tm -> Bool
semanticallyEqual env tm1 tm2 = tm2nf (reduce tm1) == tm2nf (reduce tm2)
