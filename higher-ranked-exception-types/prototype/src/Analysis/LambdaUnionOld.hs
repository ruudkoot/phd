module Analysis.LambdaUnionOld (
    module Analysis.LambdaUnionOld.Syntax,
    module Analysis.LambdaUnionOld.Reduce,
    module Analysis.LambdaUnionOld.Equality
) where

-- TODO: make use of the fact that terms are always fully applied
-- TODO: non-deterministic full β-reduction
-- TODO: capture-avoiding substitution
-- TODO: types (kinds)
-- TODO: generate arbitrary (well-typed) terms
-- TODO: test confluence, type preservation, uniqueness of normal forms, etc.
-- TODO: dynamic type checking

import Analysis.LambdaUnionOld.Syntax
import Analysis.LambdaUnionOld.Reduce
import Analysis.LambdaUnionOld.Equality
import Analysis.LambdaUnionOld.Print
