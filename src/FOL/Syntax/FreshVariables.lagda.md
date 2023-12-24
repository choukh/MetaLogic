---
url: fol.syntax.fresh
---

# 一阶逻辑 ▸ 语法 ▸ 新变元与闭公式

我们目前定义的公式较为宽泛, 实用上通常只需要一类称为**闭公式 (closed formula)** 的公式, 本篇将给出其定义.

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.Order

open import FOL.Language
module FOL.Syntax.FreshVariables (ℒ : Language) where
open import FOL.Syntax.Base ℒ
```

**<u>定义</u>** 我们说 `n` 在 `t` 中未使用 (或者说 `n` 对 `t` 是新变元), 当且仅当

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
freshₜFrom n t = ∀ {m} → n ≤ m → freshₜ m t
```

```agda
freshFrom : ℕ → Formula → 𝕋
freshFrom n φ = ∀ {m} → n ≤ m → fresh m φ
```

```agda
Freshₜ⃗ : ∀ {n} (t⃗ : 𝕍 Term n) → (∀ t → t ∈⃗ t⃗ → Σ n ， freshₜFrom n t) →
  Σ n ， ∀ t → t ∈⃗ t⃗ → freshₜFrom n t

Freshₜ⃗ [] H = 0 , λ _ ()
Freshₜ⃗ (t ∷ t⃗) H with H t (here refl) | Freshₜ⃗ t⃗ (λ t t∈⃗ → H t (there t∈⃗))
... | n , Hn | m , Hm = n + m , Hn+m where
  Hn+m : ∀ s → s ∈⃗ t ∷ t⃗ → freshₜFrom (n + m) s
  Hn+m s (here refl) n+m≤k = Hn $ ≤-trans (m≤m+n _ _) n+m≤k
  Hn+m s (there s∈⃗) n+m≤k = Hm s s∈⃗ $ ≤-trans (m≤n+m _ _) n+m≤k
```

```agda
Freshₜ : ∀ t → Σ n ， freshₜFrom n t
Freshₜ = term-elim
  (λ n → suc n , λ le → fresh# λ { refl → 1+n≰n le })
  (λ f t⃗ IH → let n , Hn = Freshₜ⃗ t⃗ IH in
    n , λ n≤m → fresh$̇ λ t t∈⃗ → Hn t t∈⃗ n≤m)
```

```agda
Fresh : ∀ φ → Σ n ， freshFrom n φ
Fresh ⊥̇ = 0 , (λ _ → fresh⊥̇)
Fresh (φ →̇ ψ) with Fresh φ | Fresh ψ
... | n , Hn | m , Hm = n + m , λ le → fresh→̇
  (Hn $ ≤-trans (m≤m+n _ _) le)
  (Hm $ ≤-trans (m≤n+m _ _) le)
Fresh (∀̇ φ) with Fresh φ
... | n , Hn = n , λ n≤m → fresh∀̇ $ Hn $ ≤-trans n≤m (n≤1+n _)
Fresh (R $̇ t⃗) with Freshₜ⃗ t⃗ (λ t _ → Freshₜ t)
... | n , Hn = n , λ n≤m → fresh$̇ λ t t∈⃗ → Hn t t∈⃗ n≤m
```

```agda
∀̇ⁿ : Formula → ℕ → Formula
∀̇ⁿ φ zero = φ
∀̇ⁿ φ (suc n) = ∀̇ (∀̇ⁿ φ n)
```

```agda
∀̇ⁿ-freshFrom : ∀ n m φ → freshFrom n φ → freshFrom (n ∸ m) (∀̇ⁿ φ m)
∀̇ⁿ-freshFrom n zero φ H = H
∀̇ⁿ-freshFrom n (suc m) φ H n∸sm≤k = fresh∀̇ $ ∀̇ⁿ-freshFrom n m φ H n∸m≤sk where
  n∸m≤sk : n ∸ m ≤ suc _
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

```agda
close : Formula → Formula
close φ = ∀̇ⁿ φ (Fresh φ .fst)
```

```agda
close-closed : ∀ φ → closed (close φ)
close-closed φ {m} _ with Fresh φ
... | n , Hn = ∀̇ⁿ-freshFrom n n φ Hn $ subst (_≤ m) (n∸n≡0 n) z≤n
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/FreshVariables.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.FreshVariables.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.fresh)  
> 交流Q群: 893531731
