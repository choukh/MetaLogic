module Foundation.Data.List where

open import Foundation.Prelude

open import Data.List public
  using ([_]; _++_)

open import Data.List.Membership.Propositional public
  using (_∈_)

open import Data.List.Relation.Unary.Any public
  using (Any; here; there)

open import Foundation.Data.Maybe

_[_]? : ∀ (xs : 𝕃 A) → ℕ → A ？
(x ∷ _)  [ zero ]?  = some x
(_ ∷ xs) [ suc n ]? = xs [ n ]?
_ [ _ ]? = none
