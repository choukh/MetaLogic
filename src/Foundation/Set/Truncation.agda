module Foundation.Set.Truncation where

open import Foundation.Prelude

open import Cubical.HITs.SetTruncation public
  using (∥_∥₂; ∣_∣₂)

module 𝟚 where
  import Cubical.HITs.SetTruncation as 🧊
  open Cubical.HITs.SetTruncation public
    using (map)

  squash : isSet ∥ A ∥₂
  squash = isSet←🧊 🧊.squash₂

  rec : isSet B → (A → B) → ∥ A ∥₂ → B
  rec sB = 🧊.rec $ isSet→🧊 sB

  rec2 : isSet C → (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → C
  rec2 sC = 🧊.rec2 $ isSet→🧊 sC

  elim : {P : ∥ A ∥₂ → 𝕋 ℓ} → ((a : ∥ A ∥₂) → isSet (P a))
        → ((x : A) → P ∣ x ∣₂) → (a : ∥ A ∥₂) → P a
  elim H = 🧊.elim $ isSet→🧊 ∘ H

  elim2 : {P : ∥ A ∥₂ → ∥ B ∥₂ → 𝕋 ℓ} →
          ((x : ∥ A ∥₂) (y : ∥ B ∥₂) → isSet (P x y)) →
          ((a : A) (b : B) → P ∣ a ∣₂ ∣ b ∣₂) →
          (x : ∥ A ∥₂) (y : ∥ B ∥₂) → P x y
  elim2 H = 🧊.elim2 $ isSet→🧊 ∘₂ H
