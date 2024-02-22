---
url: fol.syntax.fresh
---

# 一阶逻辑 ▸ 语法 ▸ 新变元与闭公式

我们目前定义的公式较为宽泛, 实用上通常只需要一类称为**闭公式 (closed formula)** 的公式, 本篇将给出其定义.

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.Order

open import FOL.Language.Base
module FOL.Syntax.FreshVariables (ℒ : Language) where
open import FOL.Syntax.Base ℒ

private variable
  m n : ℕ
```

## 新变元

**<u>归纳定义</u>** 我们说 `n` 是 `t` 的新变元 (或者说 `n` 在 `t` 中未使用), 当且仅当以下任一种情况成立

- `t` 是变元 `# m`, 且 `n ≢ m`.
- `t` 是函数应用 `f $̇ t⃗`, 且对于任意 `t ∈⃗ t⃗`, `n` 是 `t` 的新变元.

```agda
data freshₜ (n : ℕ) : Term → 𝕋 where
  fresh# : ∀ {m} → n ≢ m → freshₜ n (# m)
  fresh$̇ : ∀ {f t⃗} → (∀ t → t ∈⃗ t⃗ → freshₜ n t) → freshₜ n (f $̇ t⃗)

fresh#-elim : ∀ {n m} → freshₜ n (# m) → n ≢ m
fresh#-elim (fresh# p) = p

fresh$̇-elim : ∀ {n f t⃗} → freshₜ n (f $̇ t⃗) → (∀ t → t ∈⃗ t⃗ → freshₜ n t)
fresh$̇-elim (fresh$̇ p) = p
```

**<u>归纳定义</u>** 我们说 `n` 是 `φ` 的新变元 (或者说 `n` 在 `φ` 中未使用), 当且仅当以下任一种情况成立

- `φ` 是恒假式 `⊥̇`.
- `φ` 是蕴含式 `φ →̇ ψ`, 且 `n` 是 `φ` 和 `ψ` 的新变元.
- `φ` 是全称量化式 `∀̇ φ`, 且 `suc n` 是 `φ` 的新变元.
- `φ` 是关系应用 `R $̇ t⃗`, 且 `n` 是任意 `t ∈⃗ t⃗` 的新变元.

```agda
data freshᵩ (n : ℕ) : Formula → 𝕋 where
  fresh⊥̇ : freshᵩ n ⊥̇
  fresh→̇ : ∀ {φ ψ} → freshᵩ n φ → freshᵩ n ψ → freshᵩ n (φ →̇ ψ)
  fresh∀̇ : ∀ {φ} → freshᵩ (suc n) φ → freshᵩ n (∀̇ φ)
  fresh$̇ : ∀ {R t⃗} → (∀ t → t ∈⃗ t⃗ → freshₜ n t) → freshᵩ n (R $̇ t⃗)

fresh→̇-elim : ∀ {n φ ψ} → freshᵩ n (φ →̇ ψ) → freshᵩ n φ × freshᵩ n ψ
fresh→̇-elim (fresh→̇ p q) = p , q

fresh∀̇-elim : ∀ {n φ} → freshᵩ n (∀̇ φ) → freshᵩ (suc n) φ
fresh∀̇-elim (fresh∀̇ p) = p

freshR$̇-elim : ∀ {n R t⃗} → freshᵩ n (R $̇ t⃗) → (∀ t → t ∈⃗ t⃗ → freshₜ n t)
freshR$̇-elim (fresh$̇ p) = p
```

**<u>定义</u>** 我们说 `n` 是 `Γ` 的新变元 (或者说 `n` 在 `Γ` 中未使用), 当且仅当 `n` 是每个 `φ ∈͆ Γ` 的新变元.

```agda
fresh : ℕ → Context → 𝕋
fresh n Γ = ∀ {φ} → φ ∈͆ Γ → freshᵩ n φ
```

**<u>定义</u>** 我们说 `n` (含) 以上的变元都是项 `t` (或公式 `φ`, 或语境 `Γ`) 的新变元, 当且仅当任意 `m ≥ n` 都是 `t` (或 `φ`, 或 `Γ`) 的新变元.

```agda
freshₜFrom : ℕ → Term → 𝕋
freshₜFrom n t = ∀ {m} → n ≤ m → freshₜ m t

freshᵩFrom : ℕ → Formula → 𝕋
freshᵩFrom n φ = ∀ {m} → n ≤ m → freshᵩ m φ

freshFrom : ℕ → Context → 𝕋
freshFrom n Γ = ∀ {m} → n ≤ m → fresh m Γ
```

**<u>引理</u>** 给定项的向量 `t⃗` 以及每个 `t ∈⃗ t⃗` 的一个新变元, 可以找到对任意 `t ∈⃗ t⃗` 都是新变元的一个 `n` (简称 `t⃗` 的新变元).  
**<u>证明</u>** 归纳 `t⃗` 的长度. 长度为零时虚空真. 长度为后继时取向量的头 `t` 及尾 `t⃗`. 由前提有 `t` 的新变元 `n`, 由归纳假设有 `t⃗` 的新变元 `m`. 取 `n + m` 即可. ∎

```agda
Σfreshₜ⃗ : (t⃗ : 𝕍 Term n) → (∀ t → t ∈⃗ t⃗ → Σ n ， freshₜFrom n t) →
  Σ n ， ∀ t → t ∈⃗ t⃗ → freshₜFrom n t
Σfreshₜ⃗ [] H = 0 , λ _ ()
Σfreshₜ⃗ (t ∷ t⃗) H with H t (here refl) | Σfreshₜ⃗ t⃗ (λ t t∈⃗ → H t (there t∈⃗))
... | n , Hn | m , Hm = n + m , Hn+m where
  Hn+m : ∀ s → s ∈⃗ t ∷ t⃗ → freshₜFrom (n + m) s
  Hn+m s (here refl) n+m≤k = Hn $ ≤-trans (m≤m+n _ _) n+m≤k
  Hn+m s (there s∈⃗) n+m≤k = Hm s s∈⃗ $ ≤-trans (m≤n+m _ _) n+m≤k
```

**<u>引理</u>** 任意项都能找到一个新变元.  
**<u>证明</u>** 使用项的结构归纳法. 当项是变元 `# n` 时取 `suc n` 即可. 当项是函数应用 `f $̇ t⃗` 时, 由归纳假设及引理 `Freshₜ⃗`, 有 `t⃗` 的新变元 `n`, 它就是函数应用 `f $̇ t⃗` 的新变元. ∎

```agda
Σfreshₜ : ∀ t → Σ n ， freshₜFrom n t
Σfreshₜ = term-elim
  (λ n → suc n , λ le → fresh# λ { refl → 1+n≰n le })
  (λ f t⃗ IH → let n , Hn = Σfreshₜ⃗ t⃗ IH in
    n , λ n≤m → fresh$̇ λ t t∈⃗ → Hn t t∈⃗ n≤m)
```

**<u>引理</u>** 任意公式都能找到一个新变元.  
**<u>证明</u>** 对公式的结构归纳.
- 当公式是恒假式 `⊥̇` 时取 `0` 即可.
- 当公式是蕴含式 `φ →̇ ψ` 时, 由归纳假设, 有 `φ` 的新变元 `n`, `ψ` 的新变元 `m`, 取 `n + m` 即可.
- 当公式是全称量化式 `∀̇ φ` 时, 由归纳假设, 有 `φ` 的新变元 `n`, 取 `n` 即可.
- 当公式是关系应用 `R $̇ t⃗` 时, 由归纳假设及引理 `Freshₜ⃗`, 有 `t⃗` 的新变元 `n`, 取 `n` 即可. ∎

```agda
Σfreshᵩ : ∀ φ → Σ n ， freshᵩFrom n φ
Σfreshᵩ ⊥̇ = 0 , (λ _ → fresh⊥̇)
Σfreshᵩ (φ →̇ ψ) with Σfreshᵩ φ | Σfreshᵩ ψ
... | n , Hn | m , Hm = n + m , λ le → fresh→̇
  (Hn $ ≤-trans (m≤m+n _ _) le)
  (Hm $ ≤-trans (m≤n+m _ _) le)
Σfreshᵩ (∀̇ φ) with Σfreshᵩ φ
... | n , Hn = n , λ n≤m → fresh∀̇ $ Hn $ ≤-trans n≤m (n≤1+n _)
Σfreshᵩ (R $̇ t⃗) with Σfreshₜ⃗ t⃗ (λ t _ → Σfreshₜ t)
... | n , Hn = n , λ n≤m → fresh$̇ λ t t∈⃗ → Hn t t∈⃗ n≤m
```

**<u>定义</u>** 我们把语境 `Γ` 中那些公式 `φ` 的新变元中的最大者称为语境 `Γ` 的一个新变元, 记作 `freshVar Γ`.

```agda
freshVar : Context → ℕ
freshVar Γ = foldr max 0 $ map (fst ∘ Σfreshᵩ) Γ

freshVar-≥ : φ ∈͆ Γ → Σfreshᵩ φ .fst ≤ freshVar Γ
freshVar-≥ {φ} {ψ ∷ Γ} φ∈ = foldr-preservesᵒ H _ _ $
  inj₂ $ Any-intro $ Σfreshᵩ φ .fst , ∈map-intro φ∈ refl , ≤-refl where
    H : ∀ m n → (Σfreshᵩ φ .fst ≤ m) ⊎ (Σfreshᵩ φ .fst ≤ n) → Σfreshᵩ φ .fst ≤ max m n
    H m n (inj₁ p) = ≤-trans p ≤maxˡ
    H m n (inj₂ p) = ≤-trans p ≤maxʳ
```

**<u>引理</u>** `freshVar (φ ∷ Γ)` 既是 `φ` 的新变元, 也是 `Γ` 的新变元.  
**<u>证明</u>** 依定义. ∎

```agda
freshVar∷-freshᵩ : ∀ φ Γ → freshᵩ (freshVar (φ ∷ Γ)) φ
freshVar∷-freshᵩ φ Γ = Σfreshᵩ _ .snd (freshVar-≥ {Γ = φ ∷ Γ} (here refl))

freshVar∷-fresh : ∀ φ Γ → fresh (freshVar (φ ∷ Γ)) Γ
freshVar∷-fresh φ Γ H = Σfreshᵩ _ .snd (freshVar-≥ {Γ = φ ∷ Γ} (there H))
```

## 闭公式

**<u>定义</u>** 公式 `φ` 的 `n` 次全称量化记作 `∀̇ⁿ n φ`.

```agda
∀̇ⁿ : ℕ → Formula → Formula
∀̇ⁿ zero = id
∀̇ⁿ (suc n) = ∀̇_ ∘ ∀̇ⁿ n
```

**<u>引理</u>** 如果 `n` 是 `φ` 的新变元, 那么 `n ∸ m` 是 `∀̇ⁿ m φ` 的新变元.  
**<u>证明</u>** 归纳 `m`.
- 当 `m` 是 `zero` 时, 由前提 `n` 是 `φ` 的新变元, 所以 `n ∸ zero ≡ n` 是 `∀̇ⁿ zero φ ≡ φ` 的新变元.
- 当 `m` 是 `suc m` 时, 由归纳假设有 `n ∸ m` 是 `∀̇ⁿ m φ` 的新变元, 所以 `n ∸ suc m ≡ (n ∸ m) ∸ 1` 是 `∀̇ⁿ (suc m) φ ≡ ∀̇ (∀̇ⁿ m φ)` 的新变元. ∎

```agda
∀̇ⁿ-freshᵩFrom : ∀ n m φ → freshᵩFrom n φ → freshᵩFrom (n ∸ m) (∀̇ⁿ m φ)
∀̇ⁿ-freshᵩFrom n zero φ H = H
∀̇ⁿ-freshᵩFrom n (suc m) φ H n∸sm≤k = fresh∀̇ $ ∀̇ⁿ-freshᵩFrom n m φ H n∸m≤sk where
  n∸m≤sk : n ∸ m ≤ suc _
  n∸m≤sk = ≤-trans le (+-monoʳ-≤ 1 n∸sm≤k) where
    le : n ∸ m ≤ suc (n ∸ suc m)
    le = subst (n ∸ m ≤_) (cong suc eq) (m≤n+m∸n (n ∸ m) 1) where
      eq = n ∸ suc m    ≡⟨ cong (n ∸_) (+-comm 1 m) ⟩
           n ∸ (m + 1)  ≡˘⟨ ∸-+-assoc n m 1 ⟩
           n ∸ m ∸ 1    ∎
```

**<u>定义</u>** `0` 是其新变元 (即没有未使用变元) 的公式叫做闭公式.

```agda
closed : Formula → 𝕋
closed = freshᵩFrom 0
```

**<u>定义</u>** 给定公式 `φ`, 取其新变元 `n`, 对 `φ` 做 `n` 次全称量化, 得到的公式叫做 `φ` 的最大全称量化, 记作 `∀̇⋯ φ`.

```agda
∀̇⋯ : Formula → Formula
∀̇⋯ φ = ∀̇ⁿ (Σfreshᵩ φ .fst) φ
```

**<u>定理</u>** 对任意 `φ`, `∀̇⋯ φ` 是闭公式.  
**<u>证明</u>** 取 `φ` 的新变元 `n`, 由引理 `∀̇ⁿ-freshᵩFrom`, `∀̇⋯ φ` 的新变元是 `n ∸ n ≡ 0`, 所以 `∀̇⋯ φ` 是闭公式. ∎

```agda
∀̇⋯closed : ∀ φ → closed (∀̇⋯ φ)
∀̇⋯closed φ {m} _ with Σfreshᵩ φ
... | n , Hn = ∀̇ⁿ-freshᵩFrom n n φ Hn $ subst (_≤ m) (n∸n≡0 n) z≤n
```

**<u>定义</u>** 由闭公式组成的理论叫做闭理论.

```agda
closedᵀ : Theory → 𝕋
closedᵀ 𝒯 = ∀ {φ} → φ ∈ 𝒯 → closed φ

ClosedTheory : 𝕋₁
ClosedTheory = Σ Theory closedᵀ
```

## 命题性

**<u>事实</u>** “是闭公式” 和 “是闭理论” 是谓词.  
**<u>证明</u>** 根源在于 `fresh#` 的前提 `n ≢ m`, 也即 `⊥` 的命题性. 分别对 `freshₜ` 和 `fresh` 归纳即得. ∎

```agda
isPropFreshₜ : ∀ t → isProp (freshₜ n t)
isPropFreshₜ = term-elim
  (λ { _ (fresh# p) (fresh# q) → cong fresh# $ isProp¬ p q })
  (λ { f t⃗ IH (fresh$̇ p) (fresh$̇ q) → cong fresh$̇ $ isPropΠ2 IH p q })

isPropFreshᵩ : ∀ {φ} → isProp (freshᵩ n φ)
isPropFreshᵩ {φ = ⊥̇} fresh⊥̇ fresh⊥̇ = refl
isPropFreshᵩ {φ = _ →̇ _} (fresh→̇ p₁ p₂) (fresh→̇ q₁ q₂) = cong2 fresh→̇ (isPropFreshᵩ p₁ q₁) (isPropFreshᵩ p₂ q₂)
isPropFreshᵩ {φ = ∀̇ _} (fresh∀̇ p) (fresh∀̇ q) = cong fresh∀̇ (isPropFreshᵩ p q)
isPropFreshᵩ {φ = _ $̇ _} (fresh$̇ p) (fresh$̇ q) = cong fresh$̇ (isPropΠ2 (λ t _ → isPropFreshₜ t) p q)

isPropClosed : isProp (closed φ)
isPropClosed = isPropΠ̅ λ _ → isProp→ isPropFreshᵩ

isPropClosedᵀ : isProp (closedᵀ 𝒯)
isPropClosedᵀ = isPropΠ̅ λ _ → isPropΠ λ _ → isPropClosed
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/FreshVariables.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.FreshVariables.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.fresh)  
> 交流Q群: 893531731
