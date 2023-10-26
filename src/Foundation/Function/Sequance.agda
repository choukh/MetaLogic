module Foundation.Function.Sequance where

open import Foundation.Prelude

infix 8 _∷ₛ_

Seq : 𝕋 ℓ → 𝕋 ℓ
Seq A = ℕ → A

_∷ₛ_ : A → Seq A → Seq A
(t ∷ₛ σ) zero = t
(t ∷ₛ σ) (suc n) = σ n
