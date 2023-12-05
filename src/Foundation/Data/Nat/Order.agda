module Foundation.Data.Nat.Order where

open import Data.Nat public
  using (_≤_)
open import Data.Nat.Properties public
  using (
    ≤-trans;
    1+n≰n;
    m≤m+n; m≤n+m;
    +-monoʳ-≤;
    ∸-+-assoc; m≤n+m∸n)
