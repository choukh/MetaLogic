module Foundation.Prelude.Builtin where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (Set to 𝒰; lsuc to _⁺)

variable
  ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C : 𝒰 ℓ

open import Agda.Builtin.Unit public
  using (⊤; tt)

open import Agda.Builtin.Bool public
  using (true; false)
  renaming (Bool to 𝔹)

open import Agda.Builtin.Nat public
  using (zero; suc)
  renaming (Nat to ℕ)

open import Agda.Builtin.Sigma public
  using (Σ; _,_; fst; snd)

open import Agda.Builtin.List public
  using ([]; _∷_)
  renaming (List to 𝕃)

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _＝_)

open import Agda.Builtin.Cubical.Path public
  using ()
  renaming (_≡_ to _⥱_)
