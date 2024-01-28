module Foundation.Data.Nat.Order where

open import Foundation.Data.Nat

open import Data.Nat public
  using (
    _≤_; z≤n
    )
open import Data.Nat.Properties as ℕ public
  using (
    ≤-refl; ≤-trans;
    n≤1+n; 1+n≰n;
    m≤m+n; m≤n+m;
    +-monoʳ-≤;
    n∸n≡0; ∸-+-assoc; m≤n+m∸n)

≤maxˡ : ∀ {m n} → m ≤ max m n
≤maxˡ = ℕ.m≤m⊔n _ _

≤maxʳ : ∀ {m n} → m ≤ max n m
≤maxʳ = ℕ.m≤n⊔m _ _
