module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Logic.Iff
open import Foundation.Logic.ConstructiveEpsilon

open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Functions.Injection

open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete
open import Foundation.Relation.Unary.Countable

module MaybeView where

  _enumerates_ : (ℕ → A ？) → A → 𝕋 _
  f enumerates x = ∃ n ⸴ f n ＝ some x

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ⸴ ∀ (x : A) → f enumerates x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ⸴ ∀ x → P x ↔ f enumerates x

  Enum↔Enumℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤* {ℓ}
  Enum↔Enumℙ = ⇒: (λ (f , H) → f , λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt*))
               ⇐: (λ (f , H) → f , λ x → H x .⇒ tt*)

  enumerable : 𝕋 ℓ → 𝕋 _
  enumerable A = ∥ Enum A ∥₁

  enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
  enumerableℙ P = ∥ Enumℙ P ∥₁

  discrete→enumerable→countable : discrete A → enumerable A → countable A
  discrete→enumerable→countable {A} disA = rec₁ is₁ H where
    H : Enum A → countable A
    H (f , H) = ∣ g₁ , g₁-inj ∣₁ where
      g : ∀ x → Σ n ⸴ f n ＝ some x
      g x = ε sets dis (H x) where
        sets : isSets (λ n → f n ＝ some x)
        sets n = isProp→isSet $ (isSetMaybe $ discrete→isSet disA) _ _
        dis : ∀ n → Dec (f n ＝ some x)
        dis n = (discreteMaybe disA) _ _
      g₁ : A → ℕ
      g₁ = fst ∘ g
      g₂ : ∀ x → f (g₁ x) ＝ some x
      g₂ = snd ∘ g
      g₁-inj : injective g₁
      g₁-inj {x} {y} eq = some-inj $
        some x   ＝˘⟨ g₂ x ⟩
        f (g₁ x) ＝⟨ cong f eq ⟩
        f (g₁ y) ＝⟨ g₂ y ⟩
        some y   ∎

module ListView where
  module 𝕄 = MaybeView

  isEnumerator : (ℕ → 𝕃 A) → 𝕋 _
  isEnumerator f = ∀ n → ∃ xs ⸴ f (suc n) ＝ f n ++ xs

  Enumerator : 𝕋 ℓ → 𝕋 _
  Enumerator A = Σ (ℕ → 𝕃 A) isEnumerator

  _enumerates_ : Enumerator A → A → 𝕋 _
  f enumerates x = ∃ n ⸴ x ∈ fst f n

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ⸴ ∀ (x : A) → f enumerates x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ⸴ ∀ x → P x ↔ f enumerates x

  enumerable : 𝕋 ℓ → 𝕋 _
  enumerable A = ∥ Enum A ∥₁

  enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
  enumerableℙ P = ∥ Enumℙ P ∥₁

  Enum→𝕄 : Enum A → 𝕄.Enum A
  Enum→𝕄 ((f , isE) , H) = {!   !} , {!   !}

  enumerable→𝕄 : enumerable A → 𝕄.enumerable A
  enumerable→𝕄 = map₁ Enum→𝕄

  --enumerable←𝕄 : 𝕄.enumerable A → enumerable A
  --enumerable←𝕄 = {!   !}

  --enumerableℙ→𝕄 : enumerableℙ P → 𝕄.enumerableℙ P
  --enumerableℙ→𝕄 = {!   !}

  --enumerableℙ←𝕄 : 𝕄.enumerableℙ P → enumerableℙ P
  --enumerableℙ←𝕄 = {!   !}

  discrete→enumerable→countable : discrete A → enumerable A → countable A
  discrete→enumerable→countable disA enumA =
    𝕄.discrete→enumerable→countable disA (enumerable→𝕄 enumA)
