module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Logic.Iff
open import Foundation.Logic.ConstructiveEpsilon

open import Foundation.Data.Maybe
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

  enumerable : 𝕋 ℓ → 𝕋 _
  enumerable A = ∥ Enum A ∥₁

  enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
  enumerableℙ P = ∥ Enumℙ P ∥₁

  discrete→enumerable→countable : discrete A → enumerable A → countable A
  discrete→enumerable→countable {A} disA = rec₁ is₁ H where
    H : Enum A → countable A
    H (f , H) = ∣ g , g-inj ∣₁ where
      g : A → ℕ
      g x = fst $ ε sets dis (H x) where
        sets : isSets (λ n → f n ＝ some x)
        sets n = isProp→isSet $ (isSetMaybe $ discrete→isSet disA) _ _
        dis : ∀ n → Dec (f n ＝ some x)
        dis n = (discreteMaybe disA) _ _
      fg : ∀ x → f (g x) ＝ some x
      fg = {!   !}
      g-inj : injective g
      g-inj {x} {y} eq = some-inj $
        some x  ＝˘⟨ fg x ⟩
        f (g x) ＝⟨ cong f eq ⟩
        f (g y) ＝⟨ fg y ⟩
        some y  ∎

  countable→enumerable : countable A → enumerable A
  countable→enumerable {A} = map₁ H where
    H : A ↪ ℕ → Enum A
    H (f , f-inj) = {!   !} , {!   !} where
      g : ℕ → A ？
      g n = {!   !}

module ListView where

  _enumerates_ : (ℕ → A ？) → A → 𝕋 _
  f enumerates x = ∃ n ⸴ f n ＝ some x
