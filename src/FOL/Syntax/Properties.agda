open import FOL.Language
module FOL.Syntax.Properties (ℒ : Language) where

open import Foundation.Essential
open import Foundation.Data.Vec.SetTheoretic
  renaming (_∈_ to _∈⃗_)

open import FOL.Syntax ℒ

term-elim : {P : Term → 𝕋 ℓ} → (∀ n → P (# n)) →
  (∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → P t) → P (f $̇ t⃗)) → ∀ t → P t
term-elim H1 H2 (# n) = H1 n
term-elim {P} H1 H2 (f $̇ t⃗) = H2 f t⃗ H where
  H : ∀ {n} {t⃗ : 𝕍 Term n} t → t ∈⃗ t⃗ → P t
  H t (here refl) = term-elim H1 H2 t
  H t (there t∈⃗t⃗) = H t t∈⃗t⃗
