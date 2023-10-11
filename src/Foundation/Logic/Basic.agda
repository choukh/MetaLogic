module Foundation.Logic.Basic where

open import Foundation.Prelude.Builtin
open import Foundation.HITs.PropositionalTruncation public

open import Foundation.Data.Product public
  using ()
  renaming (_×_ to infixr 3 _∧_)

open import Foundation.Data.Sum
  using (_⊎_; inj₁; inj₂)

infixr 2 _∨_
_∨_ : (A : 𝒰 ℓ) (B : 𝒰 ℓ′) → 𝒰 _
A ∨ B = ∥ A ⊎ B ∥₁

inl : A → A ∨ B
inl x = ∣ inj₁ x ∣₁

inr : B → A ∨ B
inr x = ∣ inj₂ x ∣₁

exists : (A : 𝒰 ℓ) (P : A → 𝒰 ℓ′) → 𝒰 _
exists A B = ∥ Σ A B ∥₁

exists₋ : {A : 𝒰 ℓ} (P : A → 𝒰 ℓ′) → 𝒰 _
exists₋ {A} B = ∥ Σ A B ∥₁

∃-syntax = exists
∃₋-syntax = exists₋

infix 1 ∃-syntax ∃₋-syntax
syntax ∃-syntax A (λ x → B) = ∃ x ∶ A , B
syntax ∃₋-syntax (λ x → B) = ∃ x , B
