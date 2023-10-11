module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
open import Foundation.Logic
open import Foundation.Data.Optional

_enumerates_ : {A : 𝒰 ℓ} → (ℕ → A ？) → A → 𝒰 _
f enumerates x = ∃ n , f n ＝ some x

Enum : 𝒰 ℓ → 𝒰 _
Enum A = ∃ f , ∀ (x : A) → f enumerates x

enumerable : (A → 𝒰 ℓ) → 𝒰 _
enumerable P = ∃ f , ∀ x → P x ↔ f enumerates x
