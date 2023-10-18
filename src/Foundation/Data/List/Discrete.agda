open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete
module Foundation.Data.List.Discrete (_≟_ : discrete A) where

open import Foundation.Data.Bool
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Relation.Nullary.Decidable

index? : 𝕃 A → A → ℕ ？
index? [] x = none
index? (y ∷ xs) x = if does (x ≟ y) then some 0 else aux where
  aux : ℕ ？
  aux with index? xs x
  ... | some n = some (suc n)
  ... | none = none
