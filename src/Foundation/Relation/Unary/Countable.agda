module Foundation.Relation.Unary.Countable where

open import Foundation.Prelude
open import Foundation.Functions
open import Foundation.Logic

countable : 𝒰 ℓ → 𝒰 _
countable A = ∥ A ↠ ℕ ∥₁

countablyInfinite : 𝒰 ℓ → 𝒰 _
countablyInfinite A = ∥ A ≅ ℕ ∥₁
