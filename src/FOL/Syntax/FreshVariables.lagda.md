---
url: fol.syntax.fresh
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 新变元与闭公式

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.Order

open import FOL.Language
module FOL.Syntax.FreshVariables (ℒ : Language) where

open Language ℒ
open import FOL.Syntax.Base ℒ
```

```agda
data freshₜ (n : ℕ) : Term → 𝕋 where
  fresh# : ∀ {m} → n ≢ m → freshₜ n (# m)
  fresh$̇ : ∀ {f t⃗} → (∀ t → t ∈⃗ t⃗ → freshₜ n t) → freshₜ n (f $̇ t⃗)
```

```agda
data fresh (n : ℕ) : Formula → 𝕋 where
  fresh⊥̇ : fresh n ⊥̇
  fresh→̇ : ∀ {φ ψ} → fresh n φ → fresh n ψ → fresh n (φ →̇ ψ)
  fresh∀̇ : ∀ {φ} → fresh (suc n) φ → fresh n (∀̇ φ)
  fresh$̇ : ∀ {R t⃗} → (∀ t → t ∈⃗ t⃗ → freshₜ n t) → fresh n (R $̇ t⃗)
```

```agda
freshₜFrom : ℕ → Term → 𝕋
freshₜFrom n t = ∀ m → n ≤ m → freshₜ m t
```

```agda
freshFrom : ℕ → Formula → 𝕋
freshFrom n φ = ∀ m → n ≤ m → fresh m φ
```

```agda
Freshₜ⃗ : ∀ {n} (t⃗ : 𝕍 Term n) → (∀ t → t ∈⃗ t⃗ → Σ n ， freshₜFrom n t) →
  Σ n ， ∀ t → t ∈⃗ t⃗ → freshₜFrom n t

Freshₜ⃗ [] H = 0 , λ _ ()
Freshₜ⃗ (t ∷ t⃗) H with H t (here refl) | Freshₜ⃗ t⃗ (λ t t∈⃗ → H t (there t∈⃗))
... | n , Hn | m , Hm = n + m , Hn+m where
  Hn+m : ∀ s → s ∈⃗ t ∷ t⃗ → freshₜFrom (n + m) s
  Hn+m s (here refl) k n+m≤k = Hn k $ ≤-trans (m≤m+n _ _) n+m≤k
  Hn+m s (there s∈⃗) k n+m≤k = Hm s s∈⃗ k $ ≤-trans (m≤n+m _ _) n+m≤k
```

```agda
Freshₜ : ∀ t → Σ n ， freshₜFrom n t
Freshₜ = term-elim
  (λ n → suc n , λ _ le → fresh# λ { refl → 1+n≰n le })
  (λ f t⃗ IH → let (n , Hn) = Freshₜ⃗ t⃗ IH in
    n , λ m n≤m → fresh$̇ λ t t∈⃗ → Hn t t∈⃗ m n≤m)
```

```agda
Fresh : ∀ φ → Σ n ， freshFrom n φ
Fresh φ = {! φ  !}
```

```agda
∀̇ⁿ : Formula → ℕ → Formula
∀̇ⁿ φ zero = φ
∀̇ⁿ φ (suc n) = ∀̇ (∀̇ⁿ φ n)
```

```agda
∀̇ⁿ-freshFrom : ∀ n m φ → freshFrom n φ → freshFrom (n ∸ m) (∀̇ⁿ φ m)
∀̇ⁿ-freshFrom n zero φ H = H
∀̇ⁿ-freshFrom n (suc m) φ H k n∸sm≤k = fresh∀̇ $ ∀̇ⁿ-freshFrom n m φ H (suc k) n∸m≤sk where
  n∸m≤sk : n ∸ m ≤ suc k
  n∸m≤sk = ≤-trans le (+-monoʳ-≤ 1 n∸sm≤k) where
    le : n ∸ m ≤ suc (n ∸ suc m)
    le = subst (n ∸ m ≤_) (cong suc eq) (m≤n+m∸n (n ∸ m) 1) where
      eq = n ∸ suc m    ≡⟨ cong (n ∸_) (+-comm 1 m) ⟩
           n ∸ (m + 1)  ≡˘⟨ ∸-+-assoc n m 1 ⟩
           n ∸ m ∸ 1    ∎
```

```agda
closed : Formula → 𝕋
closed = freshFrom 0
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/FreshVariables.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.FreshVariables.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.fresh)  
> 交流Q群: 893531731
  