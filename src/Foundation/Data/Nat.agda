module Foundation.Data.Nat where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete

open import Data.Nat.Properties as ℕ public
  using (
    +-suc; +-comm
  )

discreteℕ : discrete ℕ
discreteℕ = ℕ._≟_

isSetℕ : isSet ℕ
isSetℕ = discrete→isSet discreteℕ
