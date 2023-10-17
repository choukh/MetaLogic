module Foundation.Data.Nat.AlternativeOrder where

open import Foundation.Prelude

open import Data.Nat public
  using (NonZero; nonZero)
  renaming (
    _≤′_ to _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step;
    _≥′_ to _≥_; _<′_ to _<_; _>′_ to _>_
  )

open import Data.Nat as ℕ
  using ()

open import Data.Nat.Properties as ℕ
  using (≤⇒≤′; ≤′⇒≤)

private
  map : ∀ {m n o p} → (m ℕ.≤ n → o ℕ.≤ p) → m ≤ n → o ≤ p
  map H = ≤⇒≤′ ∘ H ∘ ≤′⇒≤

  map2 : ∀ {m n o p q r} → (m ℕ.≤ n → o ℕ.≤ p → q ℕ.≤ r) → m ≤ n → o ≤ p → q ≤ r
  map2 H p q = ≤⇒≤′ $ H (≤′⇒≤ p) (≤′⇒≤ q)

z≤n : ∀ {n} → zero ≤ n
z≤n = ≤⇒≤′ $ ℕ.z≤n

s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
s≤s = map ℕ.s≤s

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans = map2 ℕ.≤-trans

m≤m+n : ∀ {m n} → m ≤ m + n
m≤m+n = ≤⇒≤′ $ ℕ.m≤m+n _ _

m≤n+m : ∀ {m n} → m ≤ n + m
m≤n+m = ≤⇒≤′ $ ℕ.m≤n+m _ _

m≤n⇒m≤o+n : ∀ {m n} o → m ≤ n → m ≤ o + n
m≤n⇒m≤o+n _ = map $ ℕ.m≤n⇒m≤o+n _

m+n≤o⇒n≤o : ∀ m {n o} → m + n ≤ o → n ≤ o
m+n≤o⇒n≤o m = map $ ℕ.m+n≤o⇒n≤o m

+-mono-≤ : ∀ {m n o p} → m ≤ n → o ≤ p → m + o ≤ n + p
+-mono-≤ = map2 ℕ.+-mono-≤

m≤m*n : ∀ m n .⦃ _ : NonZero n ⦄ → m ≤ m * n
m≤m*n _ _ = ≤⇒≤′ $ ℕ.m≤m*n _ _

m<m*n : ∀ m n .⦃ _ : NonZero m ⦄ → 1 < n → m < m * n
m<m*n _ _ = map $ ℕ.m<m*n _ _
