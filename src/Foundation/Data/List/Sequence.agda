module Foundation.Data.List.Sequence where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Data.Nat
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.Sigma

𝕃ₙ : 𝕋 ℓ → 𝕋 ℓ
𝕃ₙ A = ℕ → 𝕃 A

cumulative : 𝕃ₙ A → 𝕋 _
cumulative f = ∀ n → ∃ xs ⸴ f (suc n) ＝ f n ++ xs
