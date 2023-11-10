module Foundation.Prelude.Builtin where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (Set to 𝕋; lzero to ℓ0; lsuc to _⁺)

open import Level public
  using (Lift; lift; lower)

open import Agda.Builtin.Unit public
  using (⊤; tt)

open import Agda.Builtin.Bool public
  using (true; false)
  renaming (Bool to 𝔹)

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

open import Agda.Builtin.List public
  using ([]; _∷_)
  renaming (List to 𝕃)

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _≡_)

open import Agda.Builtin.Cubical.Path public
  using ()
  renaming (_≡_ to _≡🧊_)

open import Agda.Builtin.Sigma public
  using (Σ; fst; snd)
  renaming (_,_ to infixr 1 _,_)

variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C D T X : 𝕋 ℓ
  P Q : A → 𝕋 ℓ
  R S : A → B → 𝕋 ℓ
  P₂ Q₂ : (x : A) → P x → 𝕋 ℓ

Σ₋ : (P : A → 𝕋 ℓ) → 𝕋 _
Σ₋ {A} = Σ A

Σ-syntax = Σ
Σ₋-syntax = Σ₋

infix 1 Σ-syntax Σ₋-syntax
syntax Σ-syntax A (λ x → P) = Σ x ꞉ A ， P
syntax Σ₋-syntax (λ x → P) = Σ x ， P
