module Foundation.Data.Nat where

open import Foundation.Prelude

open import Data.Nat.Properties public
  using (+-suc; +-comm)

open import Cubical.Data.Nat
  using ()
  renaming (isSetℕ to isSetℕ🧊)

isSetℕ : isSet ℕ
isSetℕ = isSet←🧊 isSetℕ🧊
