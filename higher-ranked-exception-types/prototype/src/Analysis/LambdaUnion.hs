module Analysis.LambdaUnion (
    module Analysis.LambdaUnion.Syntax,
    module Analysis.LambdaUnion.Reduce,
    module Analysis.LambdaUnion.Equality
) where

-- TODO: make use of the fact that terms are always fully applied
-- TODO: non-deterministic full β-reduction
-- TODO: capture-avoiding substitution
-- TODO: types (kinds)
-- TODO: generate arbitrary (well-typed) terms
-- TODO: test confluence, type preservation, uniqueness of normal forms, etc.
-- TODO: dynamic type checking

import Analysis.LambdaUnion.Syntax
import Analysis.LambdaUnion.Reduce
import Analysis.LambdaUnion.Equality
import Analysis.LambdaUnion.Print
