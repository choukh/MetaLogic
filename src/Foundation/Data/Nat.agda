module Foundation.Data.Nat where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete

open import Data.Nat.Base public
  using (_∸_)

open import Data.Nat.Properties as ℕ public
  using (
    +-suc; +-comm
  )

instance
  discreteℕ : discrete ℕ
  discreteℕ = ℕ._≟_ _ _

isSetℕ : isSet ℕ
isSetℕ = discrete→isSet discreteℕ
