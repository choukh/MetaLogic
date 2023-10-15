module Foundation.Data.Nat.AlternativeOrder where

open import Foundation.Prelude

open import Data.Nat public
  using ()
  renaming (_≤′_ to _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step)
open import Data.Nat.Properties
  using (≤⇒≤′)
  renaming (m≤m+n to m≤′m+n)

m≤m+n : ∀ {m n} → m ≤ m + n
m≤m+n = ≤⇒≤′ $ m≤′m+n _ _
