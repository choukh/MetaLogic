---
url: fol.henkin
---

# 一阶逻辑 ▸ 亨金扩张

亨金扩张是指一种扩张理论的方法, 也可以指用该方法扩张后的理论. 亨金扩张的目的是使扩张后的理论满足一定的性质, 以证明一阶逻辑的完备性, 这会在下一篇讲解. 本篇先介绍亨金扩张所具有的性质, 然后讲解扩张的方法.

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder

open import FOL.Language
module FOL.HenkinExtension (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
```

## 亨金扩张的输入和输出

亨金扩张的输入要求是一个闭理论, 即由闭公式所组成的理论.

```agda
module _ ((𝒯ⁱ , 𝒯ⁱ-closed) : ClosedTheory) where
```

闭理论 `𝒯ⁱ` 的亨金扩张是一个理论 `𝒯ᵒ`, 满足

- `𝒯ᵒ` 是 `𝒯ⁱ` 的一致扩张, 即 `𝒯ᵒ` 包含 `𝒯ⁱ` 且 `𝒯ᵒ` 相对于 `𝒯ⁱ` 一致
- `𝒯ᵒ` 对证明封闭, 即 `𝒯ᵒ` 的任意可证的公式都是 `𝒯ᵒ` 的成员
- `𝒯ᵒ` 中的蕴含式满足分配性: `φ →̇ ψ` 是 `𝒯ᵒ` 的成员当且仅当 `φ` 是 `𝒯ᵒ` 的成员蕴含 `ψ` 是 `𝒯ᵒ` 的成员
- `𝒯ᵒ` 中的全称量化式满足分配性: `∀̇ φ` 是 `𝒯ᵒ` 的成员当且仅当对任意项 `t`, `φ [ t ∷]` 是 `𝒯ᵒ` 的成员

```agda
  record Output : 𝕋₁ where
    field
      𝒯ᵒ : Theory
      𝒯ᵒ-sub : 𝒯ⁱ ⊆ 𝒯ᵒ
      𝒯ᵒ-con : Con 𝒯ᵒ to 𝒯ⁱ
      𝒯ᵒ-closed-under-⊩ : ∀ φ → 𝒯ᵒ ⊩ φ → φ ∈ 𝒯ᵒ

      𝒯ᵒ-distrib-over-→̇ : ∀ φ ψ → φ →̇ ψ ∈ 𝒯ᵒ ↔ (φ ∈ 𝒯ᵒ → ψ ∈ 𝒯ᵒ)
      𝒯ᵒ-distrib-over-∀̇ : ∀ φ → ∀̇ φ ∈ 𝒯ᵒ ↔ ∀ t → φ [ t ∷] ∈ 𝒯ᵒ
```

## 亨金扩张的构造

亨金扩张其实不是一轮扩张, 而是由两轮扩张构成, 按顺序分别叫做

1. Herbelin-Ilik扩张
2. 极大一致扩张

此外, 它们可以抽象出一个共通的基础构造: 理论的无穷扩张. 我们先讲这个.

### 理论的无穷扩张

Herbelin-Ilik扩张和极大一致扩张都不是一步到位的, 而是需要可数无穷步, 每一步都是上一步的一致扩张, 这样的扩张叫做理论的无穷扩张.

```agda
module ∞-Extension
  (𝒯ᵢ : ℕ → Theory)
  (𝒯₊-sub : ∀ {n} → 𝒯ᵢ n ⊆ 𝒯ᵢ (suc n))
  (𝒯₊-con : ∀ {n} → Con 𝒯ᵢ (suc n) to 𝒯ᵢ n)
  where
```

**<u>引理</u>** 对任意 `m ≤ n`, 那么 `𝒯ᵢ n` 是 `𝒯ᵢ m` 的一致扩张.  
**<u>证明</u>** 对 `m ≤ n` 归纳, 配合步进一致扩张条件 `𝒯₊-sub` 和 `𝒯₊-con` 即得. ∎

```agda
  𝒯≤-sub : ∀ {m n} → m ≤ n → 𝒯ᵢ m ⊆ 𝒯ᵢ n
  𝒯≤-sub ≤-refl = id
  𝒯≤-sub (≤-step m≤n) ∈𝒯ₘ = 𝒯₊-sub (𝒯≤-sub m≤n ∈𝒯ₘ)

  𝒯≤-con : ∀ {m n} → m ≤ n → Con 𝒯ᵢ n to 𝒯ᵢ m
  𝒯≤-con ≤-refl = id
  𝒯≤-con (≤-step m≤n) 𝒯₊⊩⊥̇ = 𝒯≤-con m≤n (𝒯₊-con 𝒯₊⊩⊥̇)
```

**<u>定义</u>** 无穷扩张的所有步骤所得到的理论的并, 叫做无穷扩张的极限, 记作 `Λ`.

```agda
  Λ : Theory
  Λ = ⋃ᵢ 𝒯ᵢ
```

**<u>引理</u>** 无穷扩张的极限包含任意一步理论.  
**<u>证明</u>** 依定义即得. ∎

```agda
  Λ-sub : ∀ {n} → 𝒯ᵢ n ⊆ Λ
  Λ-sub = ⊆⋃ᵢ 𝒯ᵢ
```

**<u>引理</u>** 如果语境 `Γ` 包含于无穷扩张的极限, 那么 `Γ` 包含于某一步理论.  
**<u>证明</u>** 对 `Γ` 的长度归纳.

- 当 `Γ` 为空列表时, 显然成立.
- 当 `Γ` 为 `φ ∷ Γ` 时, 由归纳假设, 存在 `m` 使得 `Γ` 是 `𝒯ᵢ m` 的子集. 由前提, 存在 `n` 使得 `φ ∈ 𝒯ᵢ n`. 由 `𝒯ᵢ` 的扩张性 `𝒯ᵢ-extension`, `m` 和 `n` 的较大者 `o` 将使得 `φ ∷ Γ` 是 `𝒯ᵢ o` 的子集. ∎

```agda
  ⊆Λ→⊆𝒯ₙ : ∀ Γ → Γ ᴸ⊆ᴾ Λ → ∃ n ， Γ ᴸ⊆ᴾ 𝒯ᵢ n
  ⊆Λ→⊆𝒯ₙ [] _ = ex 0 λ ()
  ⊆Λ→⊆𝒯ₙ (φ ∷ Γ) Γ⊆l = 𝟙.map2 H (⊆Λ→⊆𝒯ₙ Γ λ φ∈Γ → Γ⊆l (there φ∈Γ)) (Γ⊆l (here refl)) where
    H : Σ m ， Γ ᴸ⊆ᴾ 𝒯ᵢ m → Σ n ， φ ∈ 𝒯ᵢ n → Σ o ， (φ ∷ Γ) ᴸ⊆ᴾ 𝒯ᵢ o
    H (m , Γ⊆𝒯ₘ) (n , φ∈𝒯ₙ) = max m n ,
      λ { (here refl) → 𝒯≤-sub ≤maxʳ φ∈𝒯ₙ
        ; (there ψ∈Γ) → 𝒯≤-sub ≤maxˡ (Γ⊆𝒯ₘ ψ∈Γ) }
```

**<u>引理</u>** 如果无穷扩张的极限可证 `φ`, 那么存在其中一步理论可证 `φ`.  
**<u>证明</u>** 由 `_⊩_` 的定义和引理 `⊆Λ→⊆𝒯ₙ` 即得. ∎

```agda
  Λ⊩→𝒯ₙ⊩ : ∀ {φ} → Λ ⊩ φ → ∃ n ， 𝒯ᵢ n ⊩ φ
  Λ⊩→𝒯ₙ⊩ (Γ , Γ⊆l , Γ⊢φ) = 𝟙.map (λ { (n , Γ⊆𝒯ᵢ) → n , Γ , Γ⊆𝒯ᵢ , Γ⊢φ }) (⊆Λ→⊆𝒯ₙ Γ Γ⊆l)
```

**<u>引理</u>** 无穷扩张的极限相对于起始理论一致.  
**<u>证明</u>** 由引理 `Λ⊩→𝒯ₙ⊩` 和 `𝒯≤-con` 即得. ∎

```agda
  Λ-con : Con Λ to 𝒯ᵢ 0
  Λ-con ∥Λ⊩⊥̇∥₁ = 𝟙.intro ∥Λ⊩⊥̇∥₁ λ Λ⊩⊥̇ →
    𝟙.intro (Λ⊩→𝒯ₙ⊩ Λ⊩⊥̇) λ { (n , 𝒯ₙ⊩⊥̇) → 𝒯≤-con z≤n ∣ 𝒯ₙ⊩⊥̇ ∣₁ }
```

**<u>引理</u>** 如果每一步扩张都是闭理论, 那么极限是闭理论.  
**<u>证明</u>** 依定义即得. ∎

```agda
  Λ-closed : (∀ n → closedTheory (𝒯ᵢ n)) → closedTheory Λ
  Λ-closed H φ = 𝟙.rec (isPredClosed φ) λ { (m , φ∈𝒯ₘ) → H m φ φ∈𝒯ₘ }
```

### Herbelin-Ilik扩张

### 极大一致扩张

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/HenkinExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.HenkinExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.henkin)  
> 交流Q群: 893531731
