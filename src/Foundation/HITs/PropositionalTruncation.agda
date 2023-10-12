module Foundation.HITs.PropositionalTruncation where

open import Foundation.Prelude

open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁)
  renaming (
    rec to rec₁; rec2 to rec₁2; rec3 to rec₁3;
    map to map₁; map2 to map₁2
    )

open import Cubical.HITs.PropositionalTruncation
  using (squash₁; elim; elim2; elim3)

is₁ : isProp ∥ A ∥₁
is₁ = isProp←🧊 squash₁

elim₁ : {P : ∥ A ∥₁ → 𝕋 ℓ} → ((a : ∥ A ∥₁) → isProp (P a))
      → ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
elim₁ H = elim $ isProp→🧊 ∘ H

elim₁2 : {P : ∥ A ∥₁ → ∥ B ∥₁ → 𝕋 ℓ}
         (Pprop : (x : ∥ A ∥₁) (y : ∥ B ∥₁) → isProp (P x y))
         (f : (a : A) (b : B) → P ∣ a ∣₁ ∣ b ∣₁)
         (x : ∥ A ∥₁) (y : ∥ B ∥₁) → P x y
elim₁2 H = elim2 $ isProp→🧊 ∘₂ H

elim₁3 : {P : ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → 𝕋 ℓ}
         (Pprop : ((x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → isProp (P x y z)))
         (g : (a : A) (b : B) (c : C) → P (∣ a ∣₁) ∣ b ∣₁ ∣ c ∣₁)
         (x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → P x y z
elim₁3 H = elim3 $ isProp→🧊 ∘₃ H