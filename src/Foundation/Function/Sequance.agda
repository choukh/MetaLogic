module Foundation.Function.Sequance where

open import Foundation.Prelude

infix 8 _;_

Seq : 𝕋 ℓ → 𝕋 ℓ
Seq A = ℕ → A

_;_ : A → Seq A → Seq A
(t ; σ) zero = t
(t ; σ) (suc n) = σ n
