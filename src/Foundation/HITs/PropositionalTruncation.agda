module Foundation.HITs.PropositionalTruncation where

open import Foundation.Prelude

open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁)
  renaming (map to map₁; map2 to map₁2)

open import Cubical.HITs.PropositionalTruncation as PT
  using (squash₁;
    rec; rec2; rec3;
    elim; elim2; elim3
  )

open PT.SetElim using (rec→Set)

is₁ : isProp ∥ A ∥₁
is₁ = isProp←🧊 squash₁

rec₁ : isProp B → (A → B) → ∥ A ∥₁ → B
rec₁ pB = rec $ isProp→🧊 pB

rec₁2 : isProp C → (A → B → C) → ∥ A ∥₁ → ∥ B ∥₁ → C
rec₁2 pC = rec2 $ isProp→🧊 pC

rec₁3 : isProp D → (A → B → C → D) → ∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → D
rec₁3 pD = rec3 $ isProp→🧊 pD

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

rec₁→Set : isSet B → (f : A → B) → constFunc f → ∥ A ∥₁ → B
rec₁→Set setB f H = rec→Set (isSet→🧊 setB) f λ x y → Eq→🧊 (H x y)

intro : ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁
intro a H = rec₁ is₁ H a

intro2 : ∥ A ∥₁ → ∥ B ∥₁ → (A → B → ∥ C ∥₁) → ∥ C ∥₁
intro2 a b H = rec₁2 is₁ H a b

intro∣ : ∥ A ∥₁ → (A → B) → ∥ B ∥₁
intro∣ = flip map₁

intro2∣ : ∥ A ∥₁ → ∥ B ∥₁ → (A → B → C) → ∥ C ∥₁
intro2∣ a b H = map₁2 H a b
