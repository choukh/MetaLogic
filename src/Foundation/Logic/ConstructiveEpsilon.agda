{-# OPTIONS --no-hidden-argument-puns #-}

module Foundation.Logic.ConstructiveEpsilon where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Data.Nat
open import Foundation.Relation.Nullary.Decidable

module _ {A : ℕ → 𝕋 ℓ} (setsA : isSets A) (decA : ∀ n → Dec (A n)) where

  data <witness : ℕ → 𝕋 ℓ where
    witness : ∀ {n} → A n → <witness n
    step↓   : ∀ {n} → <witness (suc n) → <witness n

  initial : ∀ {n} → <witness n → <witness 0
  initial {zero} w₀ = w₀
  initial {suc n} wₛ = initial (step↓ wₛ)

  search : ∀ n → <witness n → Σ ℕ A
  search n wₙ with decA n
  search n wₙ          | yes p = n , p
  search n (witness p) | no ¬p = exfalso (¬p p)
  search n (step↓ wₛ)  | no ¬p = search (suc n) wₛ

  constSearch : ∀ {n} → constFunc (search n)
  constSearch {n} w w' with
       decA n | w         | w'
  ... | yes p | _         | _         = refl
  ... | no ¬p | witness p | _         = exfalso (¬p p)
  ... | no ¬p | _         | witness p = exfalso (¬p p)
  ... | no ¬p | step↓ w   | step↓ w'  = constSearch w w'

  minWit : Σ ℕ A → Σ ℕ A
  minWit (_ , p) = search 0 $ initial $ witness p

  constMinWit : constFunc minWit
  constMinWit (_ , pₙ) (_ , qₘ) = constSearch (initial $ witness pₙ) (initial $ witness qₘ)

  ε : ∃ ℕ A → Σ ℕ A
  ε = rec₁→Set (isSetΣ isSetℕ setsA) minWit constMinWit
