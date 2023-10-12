module Foundation.Prelude.Builtin where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (Set to 𝕋; lsuc to _⁺)

variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C : 𝕋 ℓ
  P : A → 𝕋 ℓ
  P₂ : (x : A) → P x → 𝕋 ℓ

open import Agda.Builtin.Unit public
  using (⊤; tt)

open import Agda.Builtin.Bool public
  using (true; false)
  renaming (Bool to 𝔹)

open import Agda.Builtin.Nat public
  using (zero; suc)
  renaming (Nat to ℕ)

open import Agda.Builtin.List public
  using ([]; _∷_)
  renaming (List to 𝕃)

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _＝_)

open import Agda.Builtin.Cubical.Path public
  using ()
  renaming (_≡_ to _⥱_)

open import Agda.Builtin.Sigma public
  using (Σ; _,_; fst; snd)

Σ₋ : (P : A → 𝕋 ℓ) → 𝕋 _
Σ₋ {A} = Σ A

Σ-syntax = Σ
Σ₋-syntax = Σ₋

infix 1 Σ-syntax Σ₋-syntax
syntax Σ-syntax A (λ x → P) = Σ x ∶ A ⸴ P
syntax Σ₋-syntax (λ x → P) = Σ x ⸴ P
