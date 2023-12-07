module Foundation.Prop.Logic where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function
open import Foundation.Prop.Truncation

open import Foundation.Data.Empty
open import Foundation.Relation.Nullary.Negation

open import Foundation.Data.Sigma
  using (_×_)

open import Foundation.Data.Sum
  using (_⊎_; inj₁; inj₂)

exfalso₁ : ∥ A ∥₁ → ¬ A → B
exfalso₁ a ¬a = exfalso $ 𝟙.rec isProp⊥ ¬a a

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

∃̅ : (P : A → 𝕋 ℓ′) → 𝕋 _
∃̅ P = ∥ Σ̅ P ∥₁

∃-syntax = ∃
∃̅-syntax = ∃̅

infix 1 ∃-syntax ∃̅-syntax
syntax ∃-syntax A (λ x → P) = ∃ x ꞉ A ， P
syntax ∃̅-syntax (λ x → P) = ∃ x ， P

ex : (a : A) (H : P a) → ∃ A P
ex a H = ∣ a , H ∣₁
