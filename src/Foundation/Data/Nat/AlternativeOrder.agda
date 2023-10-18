module Foundation.Data.Nat.AlternativeOrder where

open import Foundation.Prelude

open import Data.Nat public
  using (NonZero; nonZero)
  renaming (
    _≤′_ to _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step;
    _≥′_ to _≥_; _<′_ to _<_; _>′_ to _>_
  )

open import Data.Nat.Properties public
  using ()
  renaming (z≤′n to z≤n; s≤′s to s≤s)

open import Data.Nat as ℕ
  using ()

open import Data.Nat.Properties as ℕ
  using (≤⇒≤′; ≤′⇒≤)

private
  variable m n o p q r : ℕ

  map : (m ℕ.≤ n → o ℕ.≤ p) → m ≤ n → o ≤ p
  map H = ≤⇒≤′ ∘ H ∘ ≤′⇒≤

  map2 : (m ℕ.≤ n → o ℕ.≤ p → q ℕ.≤ r) → m ≤ n → o ≤ p → q ≤ r
  map2 H p q = ≤⇒≤′ $ H (≤′⇒≤ p) (≤′⇒≤ q)

≤-trans : m ≤ n → n ≤ o → m ≤ o
≤-trans = map2 ℕ.≤-trans

m≤m+n : m ≤ m + n
m≤m+n = ≤⇒≤′ $ ℕ.m≤m+n _ _

m≤n+m : m ≤ n + m
m≤n+m = ≤⇒≤′ $ ℕ.m≤n+m _ _

m≤n⇒m≤o+n : ∀ o → m ≤ n → m ≤ o + n
m≤n⇒m≤o+n _ = map $ ℕ.m≤n⇒m≤o+n _

m+n≤o⇒n≤o : ∀ m → m + n ≤ o → n ≤ o
m+n≤o⇒n≤o m = map $ ℕ.m+n≤o⇒n≤o m

+-monoˡ-≤ : ∀ o → m ≤ n → m + o ≤ n + o
+-monoˡ-≤ o = map $ ℕ.+-monoˡ-≤ o

+-monoʳ-≤ : ∀ o → m ≤ n → o + m ≤ o + n
+-monoʳ-≤ o = map $ ℕ.+-monoʳ-≤ o

+-mono-≤ : m ≤ n → o ≤ p → m + o ≤ n + p
+-mono-≤ = map2 ℕ.+-mono-≤

+-cancelˡ-≤ : ∀ m n o → m + n ≤ m + o → n ≤ o
+-cancelˡ-≤ m n o = map (ℕ.+-cancelˡ-≤ m n o)

+-cancelʳ-≤ : ∀ m n o → n + m ≤ o + m → n ≤ o
+-cancelʳ-≤ m n o = map (ℕ.+-cancelʳ-≤ m n o)

m≤m*n : ∀ m n .⦃ _ : NonZero n ⦄ → m ≤ m * n
m≤m*n _ _ = ≤⇒≤′ $ ℕ.m≤m*n _ _

m<m*n : ∀ m n .⦃ _ : NonZero m ⦄ → 1 < n → m < m * n
m<m*n _ _ = map $ ℕ.m<m*n _ _
