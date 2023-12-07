module Foundation.Prop.Truncation where

open import Foundation.Prelude

open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁)

module 𝟙 where
  open Cubical.HITs.PropositionalTruncation public
    using (map; map2)
  import Cubical.HITs.PropositionalTruncation as 🧊

  squash : isProp ∥ A ∥₁
  squash = isProp←🧊 🧊.squash₁

  rec : isProp B → (A → B) → ∥ A ∥₁ → B
  rec pB = 🧊.rec $ isProp→🧊 pB

  rec2 : isProp C → (A → B → C) → ∥ A ∥₁ → ∥ B ∥₁ → C
  rec2 pC = 🧊.rec2 $ isProp→🧊 pC

  rec3 : isProp D → (A → B → C → D) → ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → D
  rec3 pD = 🧊.rec3 $ isProp→🧊 pD

  elim : {P : ∥ A ∥₁ → 𝕋 ℓ} → ((a : ∥ A ∥₁) → isProp (P a))
        → ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
  elim H = 🧊.elim $ isProp→🧊 ∘ H

  elim2 : {P : ∥ A ∥₁ → ∥ B ∥₁ → 𝕋 ℓ} →
          ((x : ∥ A ∥₁) (y : ∥ B ∥₁) → isProp (P x y)) →
          ((a : A) (b : B) → P ∣ a ∣₁ ∣ b ∣₁) →
          (x : ∥ A ∥₁) (y : ∥ B ∥₁) → P x y
  elim2 H = 🧊.elim2 $ isProp→🧊 ∘₂ H

  elim3 : {P : ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → 𝕋 ℓ} →
          (((x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → isProp (P x y z))) →
          ((a : A) (b : B) (c : C) → P (∣ a ∣₁) ∣ b ∣₁ ∣ c ∣₁) →
          (x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → P x y z
  elim3 H = 🧊.elim3 $ isProp→🧊 ∘₃ H

  rec→Set : isSet B → (f : A → B) → isId f → ∥ A ∥₁ → B
  rec→Set setB f H = 🧊.SetElim.rec→Set (isSet→🧊 setB) f λ x y → Eq→🧊 (H x y)

  rec→1 : (A → ∥ B ∥₁) → ∥ A ∥₁ → ∥ B ∥₁
  rec→1 H a = rec squash H a

  intro : ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁
  intro a H = rec squash H a

  intro2 : ∥ A ∥₁ → ∥ B ∥₁ → (A → B → ∥ C ∥₁) → ∥ C ∥₁
  intro2 a b H = rec2 squash H a b
