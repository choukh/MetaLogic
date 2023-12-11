open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete
module Foundation.Data.List.Discrete ⦃ dA : discrete A ⦄ where

open import Foundation.Data.Empty
open import Foundation.Data.Bool
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic
open import Foundation.Relation.Nullary.Decidable

_[_]⁻¹? : 𝕃 A → A → ℕ ？
[] [ x ]⁻¹? = none
(y ∷ xs) [ x ]⁻¹? = if does (x ≟ y) then some 0 else aux where
  aux : ℕ ？
  aux with xs [ x ]⁻¹?
  ... | some n = some (suc n)
  ... | none = none

∈→Σ[]⁻¹? : {xs : 𝕃 A} {x : A} → x ∈ xs → Σ n ， xs [ x ]⁻¹? ≡ some n
∈→Σ[]⁻¹? {y ∷ xs} {x} _ with x ≟ y
...                    | yes p = 0 , refl
∈→Σ[]⁻¹? (here p)     | no ¬p = exfalso (¬p p)
∈→Σ[]⁻¹? (there x∈xs) | no ¬p with ∈→Σ[]⁻¹? x∈xs
... | n , H rewrite H = suc n , refl

index-inv : (xs : 𝕃 A) {x : A} {n : ℕ} → xs [ x ]⁻¹? ≡ some n → xs [ n ]? ≡ some x
index-inv (y ∷ xs) {x} H with x ≟ y
index-inv _        refl | yes refl = refl
...                     | no ¬p with xs [ x ]⁻¹? in eq
index-inv (y ∷ xs) refl | no ¬p | some k = index-inv xs eq
