module Foundation.Data.Nat.AlternativeOrder where

open import Foundation.Prelude
open import Foundation.Data.Sum
open import Foundation.Relation.Nullary.Negation
open import Foundation.Relation.Binary.Core using (Rel)

open import Data.Nat public
  using (NonZero; nonZero)
  renaming (
    _≤′_ to infix 5 _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step;
    _≥′_ to infix 5 _≥_;
    _<′_ to infix 5 _<_;
    _>′_ to infix 5 _>_;
    _⊔_ to max
  )

open import Data.Nat.Properties as ℕ public
  using (≤⇒≤′; ≤′⇒≤)
  renaming (z≤′n to z≤n; s≤′s to s≤s)

import Data.Nat as ℕ

infix 5 _≰_

_≰_ : Rel ℕ
a ≰ b = ¬ (a ≤ b)

private
  variable m n o p q r : ℕ

  map : (m ℕ.≤ n → o ℕ.≤ p) → m ≤ n → o ≤ p
  map H = ≤⇒≤′ ∘ H ∘ ≤′⇒≤

  map2 : (m ℕ.≤ n → o ℕ.≤ p → q ℕ.≤ r) → m ≤ n → o ≤ p → q ≤ r
  map2 H p q = ≤⇒≤′ $ H (≤′⇒≤ p) (≤′⇒≤ q)

------------------------------------------------------------------------
-- Relational properties of _≤_

≤-trans : m ≤ n → n ≤ o → m ≤ o
≤-trans = map2 ℕ.≤-trans

≤-total : ∀ m n → m ≤ n ⊎ n ≤ m
≤-total m n with ℕ.≤-total m n
... | inj₁ x = inj₁ (≤⇒≤′ x)
... | inj₂ y = inj₂ (≤⇒≤′ y)

1+n≰n : 1 + n ≰ n
1+n≰n = ℕ.1+n≰n ∘ ≤′⇒≤

------------------------------------------------------------------------
-- Relational properties of _<_

<-trans : m < n → n < o → m < o
<-trans = map2 ℕ.<-trans

------------------------------------------------------------------------
-- Relationships between _≤_ nad _<_

<⇒≤ : m < n → m ≤ n
<⇒≤ = map ℕ.<⇒≤

≤-<-trans : m ≤ n → n < o → m < o
≤-<-trans = map2 ℕ.≤-<-trans

<-≤-trans : m < n → n ≤ o → m < o
<-≤-trans = map2 ℕ.<-≤-trans

≤-<-connex : ∀ m n → m ≤ n ⊎ m > n
≤-<-connex m n with ℕ.≤-<-connex m n
... | inj₁ x = inj₁ (≤⇒≤′ x)
... | inj₂ y = inj₂ (≤⇒≤′ y)

<-≤-connex : ∀ m n → m < n ⊎ m ≥ n
<-≤-connex m n with ℕ.<-≤-connex m n
... | inj₁ x = inj₁ (≤⇒≤′ x)
... | inj₂ y = inj₂ (≤⇒≤′ y)

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

m≤m+n : m ≤ m + n
m≤m+n = ≤⇒≤′ $ ℕ.m≤m+n _ _

m≤n+m : m ≤ n + m
m≤n+m = ≤⇒≤′ $ ℕ.m≤n+m _ _

m≤n⇒m≤o+n : ∀ o → m ≤ n → m ≤ o + n
m≤n⇒m≤o+n _ = map $ ℕ.m≤n⇒m≤o+n _

m≤n⇒m≤n+o : ∀ o → m ≤ n → m ≤ n + o
m≤n⇒m≤n+o _ = map $ ℕ.m≤n⇒m≤n+o _

m+n≤o⇒n≤o : ∀ m → m + n ≤ o → n ≤ o
m+n≤o⇒n≤o _ = map $ ℕ.m+n≤o⇒n≤o _

+-monoˡ-≤ : ∀ o → m ≤ n → m + o ≤ n + o
+-monoˡ-≤ _ = map $ ℕ.+-monoˡ-≤ _

+-monoʳ-≤ : ∀ o → m ≤ n → o + m ≤ o + n
+-monoʳ-≤ _ = map $ ℕ.+-monoʳ-≤ _

+-mono-≤ : m ≤ n → o ≤ p → m + o ≤ n + p
+-mono-≤ = map2 ℕ.+-mono-≤

+-cancelˡ-≤ : ∀ m n o → m + n ≤ m + o → n ≤ o
+-cancelˡ-≤ m n o = map (ℕ.+-cancelˡ-≤ m n o)

+-cancelʳ-≤ : ∀ m n o → n + m ≤ o + m → n ≤ o
+-cancelʳ-≤ m n o = map (ℕ.+-cancelʳ-≤ m n o)

------------------------------------------------------------------------
-- Properties of max and _≤_

≤maxˡ : ∀ {m n} → m ≤ max m n
≤maxˡ = ≤⇒≤′ $ ℕ.m≤m⊔n _ _

≤maxʳ : ∀ {m n} → m ≤ max n m
≤maxʳ = ≤⇒≤′ $ ℕ.m≤n⊔m _ _

------------------------------------------------------------------------
-- Properties of _+_ and _<_

m<m+n : ∀ m {n} → n > 0 → m < m + n
m<m+n _ = map $ ℕ.m<m+n _

m<n+m : ∀ m {n} → n > 0 → m < n + m
m<n+m _ = map $ ℕ.m<n+m _

+-mono-<-≤ : m < n → o ≤ p → m + o < n + p
+-mono-<-≤ = map2 ℕ.+-mono-<-≤

+-mono-≤-< : m ≤ n → o < p → m + o < n + p
+-mono-≤-< = map2 ℕ.+-mono-≤-<

------------------------------------------------------------------------
-- Properties of _*_ and _≤_/_<_

m≤m*n : ∀ m n .⦃ _ : NonZero n ⦄ → m ≤ m * n
m≤m*n _ _ = ≤⇒≤′ $ ℕ.m≤m*n _ _

m<m*n : ∀ m n .⦃ _ : NonZero m ⦄ → 1 < n → m < m * n
m<m*n _ _ = map $ ℕ.m<m*n _ _
