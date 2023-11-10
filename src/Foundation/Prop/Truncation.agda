module Foundation.Prop.Truncation where

open import Foundation.Prelude

open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁)
  renaming (map to map1; map2 to map1²)

open import Cubical.HITs.PropositionalTruncation as PT
  using (squash₁;
    rec; rec2; rec3;
    elim; elim2; elim3
  )

is1 : isProp ∥ A ∥₁
is1 = isProp←🧊 squash₁

rec1→p : isProp B → (A → B) → ∥ A ∥₁ → B
rec1→p pB = rec $ isProp→🧊 pB

rec1²→p : isProp C → (A → B → C) → ∥ A ∥₁ → ∥ B ∥₁ → C
rec1²→p pC = rec2 $ isProp→🧊 pC

rec1³→p : isProp D → (A → B → C → D) → ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → D
rec1³→p pD = rec3 $ isProp→🧊 pD

elim1→p : {P : ∥ A ∥₁ → 𝕋 ℓ} → ((a : ∥ A ∥₁) → isProp (P a))
      → ((x : A) → P ∣ x ∣₁) → (a : ∥ A ∥₁) → P a
elim1→p H = elim $ isProp→🧊 ∘ H

elim1²→p : {P : ∥ A ∥₁ → ∥ B ∥₁ → 𝕋 ℓ} →
         ((x : ∥ A ∥₁) (y : ∥ B ∥₁) → isProp (P x y)) →
         ((a : A) (b : B) → P ∣ a ∣₁ ∣ b ∣₁) →
         (x : ∥ A ∥₁) (y : ∥ B ∥₁) → P x y
elim1²→p H = elim2 $ isProp→🧊 ∘₂ H

elim1³→p : {P : ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → 𝕋 ℓ} →
         (((x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → isProp (P x y z))) →
         ((a : A) (b : B) (c : C) → P (∣ a ∣₁) ∣ b ∣₁ ∣ c ∣₁) →
         (x : ∥ A ∥₁) (y : ∥ B ∥₁) (z : ∥ C ∥₁) → P x y z
elim1³→p H = elim3 $ isProp→🧊 ∘₃ H

rec1→s : isSet B → (f : A → B) → isId f → ∥ A ∥₁ → B
rec1→s setB f H = PT.SetElim.rec→Set (isSet→🧊 setB) f λ x y → Eq→🧊 (H x y)

rec1→1 : (A → ∥ B ∥₁) → ∥ A ∥₁ → ∥ B ∥₁
rec1→1 H a = rec1→p is1 H a

intro1→1 : ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁
intro1→1 a H = rec1→p is1 H a

intro1²→1 : ∥ A ∥₁ → ∥ B ∥₁ → (A → B → ∥ C ∥₁) → ∥ C ∥₁
intro1²→1 a b H = rec1²→p is1 H a b
