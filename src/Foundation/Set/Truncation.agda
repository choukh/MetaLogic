module Foundation.Set.Truncation where

open import Foundation.Prelude

open import Cubical.HITs.SetTruncation public
  using (∥_∥₂; ∣_∣₂)
  renaming (map to map2)

open import Cubical.HITs.SetTruncation as PT
  using (squash₂;
    rec; rec2;
    elim; elim2
  )

is2 : isSet ∥ A ∥₂
is2 = isSet←🧊 squash₂

rec2→s : isSet B → (A → B) → ∥ A ∥₂ → B
rec2→s sB = rec $ isSet→🧊 sB

rec2²→s : isSet C → (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → C
rec2²→s sC = rec2 $ isSet→🧊 sC

elim2→s : {P : ∥ A ∥₂ → 𝕋 ℓ} → ((a : ∥ A ∥₂) → isSet (P a))
      → ((x : A) → P ∣ x ∣₂) → (a : ∥ A ∥₂) → P a
elim2→s H = elim $ isSet→🧊 ∘ H

elim2²→s : {P : ∥ A ∥₂ → ∥ B ∥₂ → 𝕋 ℓ} →
         ((x : ∥ A ∥₂) (y : ∥ B ∥₂) → isSet (P x y)) →
         ((a : A) (b : B) → P ∣ a ∣₂ ∣ b ∣₂) →
         (x : ∥ A ∥₂) (y : ∥ B ∥₂) → P x y
elim2²→s H = elim2 $ isSet→🧊 ∘₂ H
