module Foundation.Data.Nat.Order where

open import Data.Nat public
  using (
    _≤_; z≤n
    )
open import Data.Nat.Properties public
  using (
    ≤-trans;
    n≤1+n; 1+n≰n;
    m≤m+n; m≤n+m;
    +-monoʳ-≤;
    n∸n≡0; ∸-+-assoc; m≤n+m∸n)
