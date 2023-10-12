module Foundation.Relation.Unary.Countable where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Functions.Injection

countable : 𝕋 ℓ → 𝕋 _
countable A = ∥ A ↪ ℕ ∥₁

countablyInfinite : 𝕋 ℓ → 𝕋 _
countablyInfinite A = ∥ A ≅ ℕ ∥₁

infinite : 𝕋 ℓ → 𝕋 _
infinite A = ∥ ℕ ↪ A ∥₁
