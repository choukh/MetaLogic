module Enumerability.MaybeView where

open import Foundation.Essential
open import Foundation.Data.Maybe
open import Foundation.Data.Nat.ConstructiveEpsilon

Witness : (ℕ → A ？) → A → 𝕋 _
Witness f x = Σ n ， f n ≡ some x

_witness_ : (ℕ → A ？) → A → 𝕋 _
f witness x = ∥ Witness f x ∥₁

Enum : 𝕋 ℓ → 𝕋 _
Enum A = Σ f ， ∀ (x : A) → f witness x

Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
Enumℙ P = Σ f ， ∀ x → P x ↔ f witness x

Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
Enum↔ℙ = ⇒: (λ (f , H) → f , λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
          ⇐: (λ (f , H) → f , λ x → H x .⇒ tt)

enumerable : 𝕋 ℓ → 𝕋 _
enumerable A = ∥ Enum A ∥₁

enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
enumerableℙ P = ∥ Enumℙ P ∥₁

enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
enumerable↔ℙ = ↔-map Enum↔ℙ

discr→enum→count : discrete A → enumerable A → countable A
discr→enum→count {A} disA = 𝟙.map H where
  H : Enum A → A ↣ ℕ
  H (f , H) = g₁ , g₁-inj where
    g : ∀ x → Witness f x
    g x = ε sets dis (H x) where
      sets : isSets (λ n → f n ≡ some x)
      sets n = isProp→isSet $ (isSetMaybe $ discrete→isSet disA) _ _
      dis : ∀ n → Dec (f n ≡ some x)
      dis n = (discreteMaybe disA) _ _
    g₁ : A → ℕ
    g₁ = fst ∘ g
    g₂ : ∀ x → f (g₁ x) ≡ some x
    g₂ = snd ∘ g
    g₁-inj : injective g₁
    g₁-inj {x} {y} eq = some-inj $
      some x   ≡˘⟨ g₂ x ⟩
      f (g₁ x) ≡⟨ cong f eq ⟩
      f (g₁ y) ≡⟨ g₂ y ⟩
      some y   ∎
