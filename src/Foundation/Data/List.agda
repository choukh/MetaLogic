module Foundation.Data.List where

open import Foundation.Prelude
open import Foundation.Data.Sigma

open import Data.List public
  using (map; _++_; [_])

open import Data.List.Properties public
  using (++-assoc; ++-identityʳ)

open import Foundation.Data.Maybe

_[_]? : 𝕃 A → ℕ → A ？
(x ∷ _)  [ zero ]?  = some x
(_ ∷ xs) [ suc n ]? = xs [ n ]?
_ [ _ ]? = none
