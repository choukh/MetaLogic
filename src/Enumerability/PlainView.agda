open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder
open import Enumerability.ListView.Base

module Enumerability.PlainView
  {A : 𝕋 ℓ} ⦃ _ : Enum A ⦄
  (Hₗ : ∀ n → length (enum n) > n)
  where
