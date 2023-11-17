module Foundation.Function.Sequance where

open import Foundation.Prelude

infix 8 _∷ₙ_

InfSeq : 𝕋 ℓ → 𝕋 ℓ
InfSeq A = ℕ → A

_∷ₙ_ : A → InfSeq A → InfSeq A
(t ∷ₙ σ) zero = t
(t ∷ₙ σ) (suc n) = σ n
