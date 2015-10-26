module Analysis.Infer.Join (
    join
) where

import           Analysis.Names
import           Analysis.Common

-- | Join / subtyping / least upper bounds

join :: ExnTy -> ExnTy -> ExnTy
join ExnBool ExnBool
    = ExnBool
join ExnInt ExnInt
    = ExnInt
join (ExnForall x k t) (ExnForall x' k' t')
    | k == k'   = ExnForall x k (join t (substExnTy x' x t'))
    | otherwise = error "join: kind mismatch"
join (ExnList t exn) (ExnList t' exn')
    = ExnList (join t t') (ExnUnion exn exn')
join (ExnArr t1 (ExnVar exn1) t2 exn2) (ExnArr t1' (ExnVar exn1') t2' exn2')
    | exnTyEq (error "don't use me") t1 t1', exn1 == exn1'
        -- TODO: are we sure no alpha-renaming is needed?
        = ExnArr t1 (ExnVar exn1) (join t2 t2') (ExnUnion exn2 exn2')
    | otherwise = error $ "join: function space"
join t t'
    = error $ "join: t = " ++ show t ++ "; t' = " ++ show t'

