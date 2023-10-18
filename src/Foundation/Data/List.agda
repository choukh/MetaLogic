module Foundation.Data.List where

open import Foundation.Prelude
open import Foundation.Data.Sigma

open import Data.List public
  using (map; length; _++_; [_])

open import Data.List.Properties public
  using (length-map; length-++; ++-assoc; ++-identityʳ)

open import Foundation.Data.Maybe
open import Foundation.Data.Nat.AlternativeOrder

_[_]? : 𝕃 A → ℕ → A ？
(x ∷ _)  [ zero ]?  = some x
(_ ∷ xs) [ suc n ]? = xs [ n ]?
_ [ _ ]? = none

Σ[<length]? : (xs : 𝕃 A) (n : ℕ) → n < length xs → Σ x ⸴ xs [ n ]? ＝ some x
Σ[<length]? (x ∷ xs) zero _ = x , refl
Σ[<length]? (x ∷ xs) (suc n) lt = Σ[<length]? xs n (+-cancelˡ-≤ _ _ _ lt)
