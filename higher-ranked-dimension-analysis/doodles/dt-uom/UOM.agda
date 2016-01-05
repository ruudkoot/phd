open import Data.Nat
open import Data.Integer

data Dim : Set where
  dim : ℤ -> ℤ -> Dim
  
data Real : Dim -> Set where
  real : (d : Dim) -> ℕ -> Real d

data _≡δ_ : Dim -> Dim -> Set where
  
