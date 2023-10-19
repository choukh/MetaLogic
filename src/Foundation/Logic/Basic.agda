module Foundation.Logic.Basic where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function
open import Foundation.HITs.PropositionalTruncation public

open import Foundation.Data.Empty public
open import Foundation.Data.Unit public
open import Foundation.Relation.Nullary.Negation public

open import Foundation.Data.Sigma public
  using (_×_; SigEqProp; ProdEq)

open import Foundation.Data.Sum
  using (_⊎_; inj₁; inj₂)

exfalso₁ : ∥ A ∥₁ → ¬ A → B
exfalso₁ a ¬a = exfalso $ rec1→p isProp⊥ ¬a a

infixr 3 _∧_
_∧_ = _×_

infixr 2 _∨_
_∨_ : (A : 𝕋 ℓ) (B : 𝕋 ℓ′) → 𝕋 _
A ∨ B = ∥ A ⊎ B ∥₁

inl : A → A ∨ B
inl x = ∣ inj₁ x ∣₁

inr : B → A ∨ B
inr x = ∣ inj₂ x ∣₁

∃ : (A : 𝕋 ℓ) (P : A → 𝕋 ℓ′) → 𝕋 _
∃ A P = ∥ Σ A P ∥₁

∃₋ : (P : A → 𝕋 ℓ′) → 𝕋 _
∃₋ P = ∥ Σ₋ P ∥₁

∃-syntax = ∃
∃₋-syntax = ∃₋

infix 1 ∃-syntax ∃₋-syntax
syntax ∃-syntax A (λ x → P) = ∃ x ∶ A ⸴ P
syntax ∃₋-syntax (λ x → P) = ∃ x ⸴ P

exists : (a : A) (H : P a) → ∃ A P
exists a H = ∣ a , H ∣₁
