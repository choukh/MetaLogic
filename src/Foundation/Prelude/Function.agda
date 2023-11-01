module Foundation.Prelude.Function where

open import Foundation.Prelude.Builtin

open import Function public
  using (_∘_; _∘₂_; _$_; _$-; λ-; id; flip)

-- tribute to copilot
_∘₃_ : ∀ {A₁ : 𝕋 ℓ} {A₂ : A₁ → 𝕋 ℓ′} {A₃ : (x : A₁) → A₂ x → 𝕋 ℓ″}
         {B : (x : A₁) → (y : A₂ x) → A₃ x y → 𝕋 ℓ‴}
         {C : {x : A₁} → {y : A₂ x} → {z : A₃ x y} → B x y z → 𝕋 ℓ⁗} →
       ({x : A₁} → {y : A₂ x} → {z : A₃ x y} → (w : B x y z) → C w) →
       (g : (x : A₁) → (y : A₂ x) → (z : A₃ x y) → B x y z) →
       ((x : A₁) → (y : A₂ x) → (z : A₃ x y) → C (g x y z))
f ∘₃ g = λ x y z → f (g x y z)

flip2 : ∀ {A : 𝕋 ℓ} {B : 𝕋 ℓ′} {C : 𝕋 ℓ″} {D : A → B → C → 𝕋 ℓ‴} →
        ((x : A) (y : B) (z : C) → D x y z) → ((y : B) (z : C) (x : A) → D x y z)
flip2 f y z x = f x y z

constFunc : (A → B) → 𝕋 _
constFunc f = ∀ x y → f x ≡ f y
