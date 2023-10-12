module Foundation.Functions.Injection where

open import Foundation.Prelude

injective : (A → B) → 𝕋 _
injective f = ∀ {x y} → f x ＝ f y → x ＝ y

_↪_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ↪ B = Σ (A → B) injective

↪-refl : A ↪ A
↪-refl = id , λ refl → refl

↪-trans : A ↪ B → B ↪ C → A ↪ C
↪-trans (f , f-inj) (g , g-inj) = g ∘ f , f-inj ∘ g-inj
