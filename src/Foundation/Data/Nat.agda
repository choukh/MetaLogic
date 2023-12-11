module Foundation.Data.Nat where

open import Foundation.Prelude

open import Data.Nat.Base public
  using (_∸_)

open import Data.Nat.Properties as ℕ public
  using (
    +-suc; +-comm
  )
