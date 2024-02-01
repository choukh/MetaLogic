---
url: fol.extension
---

# 一阶逻辑 ▸ 理论的扩张

扩张理论的目的是使扩张后的理论满足一定的性质, 以证明一阶逻辑的完备性, 这会在下一篇讲解. 本篇先介绍此种扩张 (以下称为完备扩张) 应具有的性质, 然后讲解该扩张的具体构造.

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder

open import FOL.Language
module FOL.TheoryExtension (ℒ : Language) where

open import FOL.Syntax.Base ℒ hiding (Γ)
open import FOL.Syntax.Discrete ℒ
open import FOL.Syntax.Enumeration ℒ
open import FOL.Syntax.FreshVariables ℒ
open import FOL.Syntax.SubstitutionFacts ℒ
open import FOL.Syntax.AdmissibleRule ℒ

private variable
  m n : ℕ
```

## 完备扩张的定义

完备扩张的输入要求是一个闭理论, 即由闭公式所组成的理论.

```agda
module _ ((𝒯ⁱ , 𝒯ⁱ-closed) : ClosedTheory) where
```

闭理论 `𝒯ⁱ` 的完备扩张是一个理论 `𝒯ᵒ`, 满足

- `𝒯ᵒ` 是 `𝒯ⁱ` 的一致扩张, 即 `𝒯ᵒ` 包含 `𝒯ⁱ` 且 `𝒯ᵒ` 相对于 `𝒯ⁱ` 一致
- `𝒯ᵒ` 对证明封闭, 即 `𝒯ᵒ` 的任意可证的公式都是 `𝒯ᵒ` 的成员
- `𝒯ᵒ` 中的蕴含式满足分配性: `φ →̇ ψ` 是 `𝒯ᵒ` 的成员当且仅当 `φ` 是 `𝒯ᵒ` 的成员蕴含 `ψ` 是 `𝒯ᵒ` 的成员
- `𝒯ᵒ` 中的全称量化式满足分配性: `∀̇ φ` 是 `𝒯ᵒ` 的成员当且仅当对任意项 `t`, `φ [ t ]₀` 是 `𝒯ᵒ` 的成员

```agda
  record CompleteExtension : 𝕋₁ where
    field
      𝒯ᵒ : Theory
      𝒯ᵒ-sub : 𝒯ⁱ ⊆ 𝒯ᵒ
      𝒯ᵒ-con : Con 𝒯ᵒ to 𝒯ⁱ
      𝒯ᵒ-closed-under-⊢ : ∀ φ → 𝒯ᵒ ⊢ᵀ φ → φ ∈ 𝒯ᵒ

      𝒯ᵒ-distrib-over-→̇ : ∀ φ ψ → φ →̇ ψ ∈ 𝒯ᵒ ↔ (φ ∈ 𝒯ᵒ → ψ ∈ 𝒯ᵒ)
      𝒯ᵒ-distrib-over-∀̇ : ∀ φ → ∀̇ φ ∈ 𝒯ᵒ ↔ ∀ t → φ [ t ]₀ ∈ 𝒯ᵒ
```

完备扩张其实不是一轮扩张, 而是由两轮扩张构成, 按顺序分别叫做

1. 极大全称扩张
2. 极大一致扩张

它们可以抽象出一个共通的基础构造: 无穷扩张. 我们先讲这个.

## 无穷扩张

极大全称扩张和极大一致扩张都不是一步到位的, 而是需要可数无穷步, 每一步都是上一步的一致扩张, 这样的扩张叫做无穷扩张.

**<u>定义</u>** 无穷扩张是理论的一个无穷序列, 其中每一项都是上一项的一致扩张.

```agda
record GeneralizedExtension : 𝕋₁ where
  constructor mkGenExt
  field
    𝒯ᵢ : ℕ → Theory
    𝒯₊-sub : 𝒯ᵢ n ⊆ 𝒯ᵢ (suc n)
    𝒯₊-con : Con 𝒯ᵢ (suc n) to 𝒯ᵢ n
```

**<u>引理</u>** 对任意 `m ≤ n`, `𝒯ᵢ n` 是 `𝒯ᵢ m` 的一致扩张.  
**<u>证明</u>** 对 `m ≤ n` 归纳, 配合步进一致扩张条件 `𝒯₊-sub` 和 `𝒯₊-con` 即得. ∎

```agda
  𝒯≤-sub : m ≤ n → 𝒯ᵢ m ⊆ 𝒯ᵢ n
  𝒯≤-sub ≤-refl = id
  𝒯≤-sub (≤-step m≤n) ∈𝒯ₘ = 𝒯₊-sub (𝒯≤-sub m≤n ∈𝒯ₘ)

  𝒯≤-con : m ≤ n → Con 𝒯ᵢ n to 𝒯ᵢ m
  𝒯≤-con ≤-refl = id
  𝒯≤-con (≤-step m≤n) 𝒯₊⊢⊥̇ = 𝒯≤-con m≤n (𝒯₊-con 𝒯₊⊢⊥̇)
```

**<u>定义</u>** 无穷扩张的所有步骤所得到的理论的并, 叫做无穷扩张的极限, 记作 `𝒯ω`.

```agda
  𝒯ω : Theory
  𝒯ω = ⋃ᵢ 𝒯ᵢ
```

**<u>引理</u>** 无穷扩张的极限包含任意一步理论.  
**<u>证明</u>** 依定义即得. ∎

```agda
  𝒯ω-sub : 𝒯ᵢ n ⊆ 𝒯ω
  𝒯ω-sub = ⊆⋃ᵢ 𝒯ᵢ
```

**<u>引理</u>** 如果语境 `Γ` 包含于无穷扩张的极限, 那么 `Γ` 包含于某一步理论.  
**<u>证明</u>** 对 `Γ` 的长度归纳.

- 当 `Γ` 为空列表时, 显然成立.
- 当 `Γ` 为 `φ ∷ Γ` 时, 由归纳假设, 存在 `m` 使得 `Γ` 是 `𝒯ᵢ m` 的子集. 由前提, 存在 `n` 使得 `φ ∈ 𝒯ᵢ n`. 由扩张性 `𝒯≤-sub`, `m` 和 `n` 的较大者 `o` 将使得 `φ ∷ Γ` 是 `𝒯ᵢ o` 的子集. ∎

```agda
  ⊆𝒯ω→⊆𝒯ₙ : ∀ Γ → Γ ᴸ⊆ᴾ 𝒯ω → ∃ n ， Γ ᴸ⊆ᴾ 𝒯ᵢ n
  ⊆𝒯ω→⊆𝒯ₙ [] _ = ex 0 λ ()
  ⊆𝒯ω→⊆𝒯ₙ (φ ∷ Γ) Γ⊆l = 𝟙.map2 H (⊆𝒯ω→⊆𝒯ₙ Γ λ φ∈Γ → Γ⊆l (there φ∈Γ)) (Γ⊆l (here refl)) where
    H : Σ m ， Γ ᴸ⊆ᴾ 𝒯ᵢ m → Σ n ， φ ∈ 𝒯ᵢ n → Σ o ， (φ ∷ Γ) ᴸ⊆ᴾ 𝒯ᵢ o
    H (m , Γ⊆𝒯ₘ) (n , φ∈𝒯ₙ) = max m n ,
      λ { (here refl) → 𝒯≤-sub ≤maxʳ φ∈𝒯ₙ
        ; (there ψ∈Γ) → 𝒯≤-sub ≤maxˡ (Γ⊆𝒯ₘ ψ∈Γ) }
```

**<u>引理</u>** 如果无穷扩张的极限可证 `φ`, 那么存在其中一步理论可证 `φ`.  
**<u>证明</u>** 由 `_⊢_` 的定义和引理 `⊆𝒯ω→⊆𝒯ₙ` 即得. ∎

```agda
  𝒯ω⊢→𝒯ₙ⊢ : ∀ {φ} → 𝒯ω ⊢ᵀ φ → ∃ n ， 𝒯ᵢ n ⊢ᵀ φ
  𝒯ω⊢→𝒯ₙ⊢ (Γ , Γ⊆l , Γ⊢φ) = 𝟙.map (λ { (n , Γ⊆𝒯ᵢ) → n , Γ , Γ⊆𝒯ᵢ , Γ⊢φ }) (⊆𝒯ω→⊆𝒯ₙ Γ Γ⊆l)
```

**<u>引理</u>** 无穷扩张的极限相对于起始理论一致.  
**<u>证明</u>** 由引理 `𝒯ω⊢→𝒯ₙ⊢` 和 `𝒯≤-con` 即得. ∎

```agda
  𝒯ω-con : Con 𝒯ω to 𝒯ᵢ 0
  𝒯ω-con ∥𝒯ω⊢⊥̇∥₁ = 𝟙.intro ∥𝒯ω⊢⊥̇∥₁ λ 𝒯ω⊢⊥̇ →
    𝟙.intro (𝒯ω⊢→𝒯ₙ⊢ 𝒯ω⊢⊥̇) λ { (n , 𝒯ₙ⊢⊥̇) → 𝒯≤-con z≤n ∣ 𝒯ₙ⊢⊥̇ ∣₁ }
```

**<u>引理</u>** 如果每一步扩张都是闭理论, 那么极限是闭理论.  
**<u>证明</u>** 依定义即得. ∎

```agda
  𝒯ω-closed : (∀ n → closedTheory (𝒯ᵢ n)) → closedTheory 𝒯ω
  𝒯ω-closed H = 𝟙.rec isPropClosed λ { (m , φ∈𝒯ₘ) → H m φ∈𝒯ₘ }
```

## 极大全称扩张

我们这里讲的极大全称扩张是 [Herbelin 和 Ilik](https://arxiv.org/abs/2401.13304) 对所谓亨金扩张的构造主义改良版本. 这里不要求先掌握原版亨金扩张, 可以直接往下看.

极大全称扩张的输入是一个闭理论, 我们将它参数化, 并且导入对集合添加元素的操作 `_⨭_`. 由于 `Formula` 是一个集合, 我们可以对公式的集合 (理论) 合法地使用 `_⨭_`.

```agda
module MaxAllExtension ((𝒯ⁱ , 𝒯ⁱ-closed) : ClosedTheory) where
  open SetOperation (discreteSet {A = Formula})
```

极大全称扩张的目的是使得输入的闭理论极大全称化. 当然, 我们的最终目的是完备化, 怎么从极大全称化推出完备化会在本文最后讲解.

**<u>定义</u>** 极大全称化: 我们说一个理论 `𝒯` 是极大全称化的, 当且仅当对 `𝒯` 的任意扩张 `𝒯′` 和任意公式 `φ`, 如果对任意项 `t`, `φ [ t ]₀ ` 都是 `𝒯′` 的定理, 那么 `∀̇ φ` 是 `𝒯′` 的定理.

```agda
  isMaxAll : Theory → 𝕋₁
  isMaxAll 𝒯 = ∀ 𝒯′ φ → 𝒯 ⊆ 𝒯′ → (∀ t → ∥ 𝒯′ ⊢ᵀ φ [ t ]₀ ∥₁) → ∥ 𝒯′ ⊢ᵀ ∀̇ φ ∥₁
```

从该定义不难看出, 所谓极大全称化, 说白了就是使所有在元层面看起来成立的全称量化事实都成为理论的内定理. 它的实现也相当直接, 就是将所有这样的事实推理全部都用对象语言写成蕴含式, 并添加到原理论中. 这些被添加的蕴含式叫做**全称公理**, 对每个公式都有一条, 如以下代码所示. 其中 `Ψ` 是公式的枚举函数, 其构造使得 `# n` 在 `Ψ n` 中未使用. 回顾可容许规则 `AllI′` 不难看出此公理也是可容许的 (相对一致的), 其严格证明会在后面给出.

```agda
  Ax : ℕ → Formula
  Ax n = Ψ n [ # n ]₀ →̇ ∀̇ Ψ n
```

由于公式有可数无穷个, 此扩张也需要可数无穷步. 其中第 `0` 步是原理论, 第 `suc n` 步是第 `n` 步的理论添加上 `Ψ n` 的全称公理 `Ax n`. 每一步所得到的理论记作 `𝒜 n`.

```agda
  𝒜 : ℕ → Theory
  𝒜 zero = 𝒯ⁱ
  𝒜 (suc n) = 𝒜 n ⨭ Ax n
```

接下来我们希望套用上一小节建立的无穷扩张框架, 说明 `𝒜` 的极限是原理论的一致扩张. 为此, 需要证明 `𝒜` 的每一步都是上一步的一致扩张.

**<u>引理</u>** `𝒜` 的每一步都是上一步的扩张.  
**<u>证明</u>** 依定义即得. ∎

```agda
  𝒜-sub : 𝒜 n ⊆ 𝒜 (suc n)
  𝒜-sub {n} = ⊆⨭ (𝒜 n)
```

**<u>引理</u>** 对任意 `φ ∈ 𝒜 n`, 任意 `m ≥ n` 都是 `φ` 的新变元.  
**<u>证明</u>** 对 `n` 归纳.

- `n` 为零时, `𝒜 0` 就是原理论 `𝒯ⁱ`. 由于 `𝒯ⁱ` 是闭理论, 所以任意 `m ≥ 0` 都是任意 `φ ∈ 𝒯ⁱ` 的新变元.
- `n` 为后继时, 有 `φ ∈ 𝒜 n ⨭ Ax n`, 分两种情况:
  - `φ` 是 `𝒜 n` 的成员, 那么由归纳假设, 任意 `m ≥ n` 都是 `φ` 的新变元.
  - `φ` 是 `Ax n`, 要证 `m` 是 `Ψ n [ # n ]₀ →̇ ∀̇ Ψ n` 的新变元, 需要分别说明 `m` 是蕴含式左右两边的新变元.
    - 对于右边, 只要证 `suc m` 是 `Ψ n` 的新变元, 由 `suc m ≥ n` 即证.
    - 对于左边, 要证对任意 `k`, 要么 `k` 是 `Ψ n` 的新变元, 要么 `m` 是项 `(# n ∷ₙ #) k` 的新变元. 讨论 `k`.
      - `k` 为零时, `(# n ∷ₙ #) k` 即为 `# n`. 由于 `n ≢ m`, `m` 是 `# n` 的新变元.
      - `k` 为后继 `suc k` 时, `(# n ∷ₙ #) k` 即为 `# k`. 讨论 `k` 与 `m` 的大小关系.
        - 若 `k < m`, 则 `k ≢ m`, 所以 `m` 是 `# k` 的新变元.
        - 若 `k ≥ m`, 则 `suc k ≥ suc m ≥ n`, 所以 `suc k` 是 `Ψ n` 的新变元.

```agda
  𝒜-fresh : n ≤ m → φ ∈ 𝒜 n → freshᵩ m φ
  𝒜-fresh {n = zero} _ φ∈ = 𝒯ⁱ-closed φ∈ (≤′⇒≤ z≤n)
  𝒜-fresh {n = suc n} {m} sn≤m = 𝟙.rec isPropFreshᵩ
    λ { (inj₁ φ∈) → 𝒜-fresh n≤m φ∈
      ; (inj₂ refl) → fresh→̇ (fresh[]ᵩ H) (fresh∀̇ (Ψ-fresh n≤sm)) }
    where
    n≤m : n ≤ m
    n≤m = ≤-trans (≤-step ≤-refl) sn≤m
    n≤sm : n ≤ suc m
    n≤sm = ≤-trans (≤-step ≤-refl) (s≤s n≤m)
    H : ∀ k → freshᵩ k (Ψ n) ⊎ freshₜ m ((# n ∷ₙ #) k)
    H zero = inj₂ $ fresh# λ { refl → 1+n≰n sn≤m }
    H (suc k) with <-≤-connex k m
    ... | inj₁ H = inj₂ $ fresh# λ { refl → 1+n≰n H }
    ... | inj₂ H = inj₁ $ Ψ-fresh (≤-trans n≤sm (s≤s H))
```

**<u>引理</u>** `𝒜` 的每一步都与上一步相对一致.  
**<u>证明</u>** 只要证 `𝒜 (suc n) ⊢ᵀ ⊥̇` 可以转化为 `𝒜 n ⊢ᵀ ⊥̇`.

给定 `𝒜 (suc n) ⊢ᵀ ⊥̇`, 由 `𝒜` 的定义和 `ImpIᵀ` 规则有 `𝒜 n ⊢ᵀ ¬̇ Ax n`, 也就是说有满足 `Γ ᴸ⊆ᴾ 𝒜 n` 的 `Γ` 满足 `Γ ⊢ ¬̇ Ax n`. 现在要证 `𝒜 n ⊢ᵀ ⊥̇`, 我们宣称 `Γ` 就是所需的语境, 也就是证 `Γ ⊢ ⊥̇`.

```agda
  𝒜-con : Con (𝒜 (suc n)) to (𝒜 n)
  𝒜-con {n} = 𝟙.map aux where
    aux : 𝒜 (suc n) ⊢ᵀ ⊥̇ → 𝒜 n ⊢ᵀ ⊥̇
    aux H₀ = Γ , Γ⊆ , Γ⊢⊥ where
      H : 𝒜 n ⊢ᵀ ¬̇ Ax n
      H = ImpIᵀ (𝒜 n) H₀
      Γ = H .fst
      Γ⊆ = H .snd .fst
      Γ⊢ = H .snd .snd
```

由于对任意 `φ` 都有 `(↑ φ) [ t ]₀ ≡ φ`, 我们可以将 `Ax n` 中的 `Ψ n` 都换成 `(↑ Ψ n) [ # 0 ]₀`, 于是有

`Γ ⊢ (¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)) [ # n ]₀`.

此处用局部无名变换, 可得

`⇞ Γ ⊢ ¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)`.

```agda
      eq : (¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)) [ # n ]₀ ≡ ¬̇ Ax n
      eq = cong (_→̇ ⊥̇) $ cong (Ψ n [ # n ]₀ →̇_) ↑[]₀
      Γ⊢′ : Γ ⊢ (¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)) [ # n ]₀
      Γ⊢′ = subst (Γ ⊢_) eq Γ⊢
      ↑Γ⊢ : ⇞ Γ ⊢ ¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)
      ↑Γ⊢ = nameless-conversion H1 H2 .⇐ Γ⊢′ where
```

此处的局部无名变换要求:

1. `n` 是 `Γ` 的新变元, 由引理 `𝒜-fresh` 即得.
2. `n` 是 `∀̇ ¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)` 的新变元, 用与 `𝒜-fresh` 的证明类似的方法可证.

```agda
        H1 : fresh n Γ
        H1 φ∈ = 𝒜-fresh ≤-refl (Γ⊆ φ∈)
        H2 : freshᵩ n (∀̇ ¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n))
        H2 = fresh∀̇ $ fresh→̇ (fresh→̇ (Ψ-fresh (≤-step ≤-refl)) (fresh∀̇ $ fresh[]ᵩ H3)) fresh⊥̇ where
          H3 : ∀ k → freshᵩ k (Ψ n) ⊎ freshₜ (suc (suc n)) (↑ₛ (# ∘ suc) k)
          H3 zero = inj₂ $ fresh# λ ()
          H3 (suc k) with <-≤-connex k n
          ... | inj₁ H = inj₂ $ fresh# λ { refl → 1+n≰n H }
          ... | inj₂ H = inj₁ $ Ψ-fresh (≤-trans H (≤-step ≤-refl))
```

最后, 注意到我们证明的 `⇞ Γ ⊢ ¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)` 违反饮者“悖论” `DP`, 所以 `Γ ⊢ ⊥̇`. ∎

```agda
      Γ⊢⊥ =                       ∅─⟨ ↑Γ⊢ ⟩
        ⇞ Γ ⊢ ¬̇ (Ψ n →̇ ↑ ∀̇ Ψ n)   ─⟨ ImpE′ ⟩
        Ψ n →̇ ↑ ∀̇ Ψ n ∷ ⇞ Γ ⊢ ⊥̇   ─⟨ ExE DP ⟩
        Γ ⊢ ⊥̇
```

至此, 我们证明了 `𝒜` 的每一步都是上一步的一致扩张, 于是由无穷扩张的引理, `𝒜` 的极限 `𝒜ω` 是原理论 `𝒯ⁱ` 的一致扩张, 且是闭理论.

```agda
  open GeneralizedExtension (mkGenExt 𝒜 𝒜-sub 𝒜-con) public
    renaming ( 𝒯ω to 𝒜ω
             ; 𝒯ω-sub to 𝒜ω-sub
             ; 𝒯ω-con to 𝒜ω-con
             ; 𝒯ω-closed to 𝒜ω-closed
             )
```

最后, 我们来说明 `𝒜ω` 是极大全称化的.

**<u>引理</u>** 对 `𝒜ω` 的任意扩张 `𝒯`, `𝒯` 到 `Ψ n [ # n ]₀` 的证明可以转化为 `𝒯` 到 `∀̇ Ψ n` 的证明.  
**<u>证明</u>** 给定 `𝒯 ⊢ᵀ Ψ n [ # n ]₀`, 我们有 `Γ ᴸ⊆ᴾ 𝒯` 满足 `Γ ⊢ Ψ n [ # n ]₀`. 现在要证 `𝒯 ⊢ᵀ ∀̇ Ψ n`, 我们宣称 `Ax n ∷ Γ` 就是要找的语境. 为此需要证明:

- `Ax n ∷ Γ ᴸ⊆ᴾ 𝒯`: 这又需要证:
  - `Ax n ∈ 𝒯`: 由于 `𝒯` 是 `𝒜ω` 的扩张, 只需证 `Ax n ∈ 𝒜ω`, 由定义显然成立.
  - `Γ ᴸ⊆ᴾ 𝒯`: 由前提即得.
- `Ax n ∷ Γ ⊢ ∀̇ Ψ n`: 如代码所示. ∎

```agda
  𝒜ω-isMaxAll-Ψ : ∀ 𝒯 → 𝒜ω ⊆ 𝒯 → 𝒯 ⊢ᵀ Ψ n [ # n ]₀ → 𝒯 ⊢ᵀ ∀̇ Ψ n
  𝒜ω-isMaxAll-Ψ {n} 𝒯 𝒜ω⊆𝒯 (Γ , Γ⊆𝒯 , Γ⊢) = Ax n ∷ Γ , ∷⊆𝒯 , ∷⊢∀̇ where
    ∷⊆𝒯 : Ax n ∷ Γ ᴸ⊆ᴾ 𝒯
    ∷⊆𝒯 (here refl) = 𝒜ω⊆𝒯 (ex (suc n) (inr refl))
    ∷⊆𝒯 (there φ∈Γ) = Γ⊆𝒯 φ∈Γ
    ∷⊢∀̇ : Ax n ∷ Γ ⊢ ∀̇ Ψ n
    ∷⊢∀̇ = ImpE H₁ H₂ where
      H₁ =                                ∅─⟨ Ctx0 ⟩
        Ax n ∷ Γ ⊢ Ψ n [ # n ]₀ →̇ (∀̇ Ψ n)
      H₂ =                                ∅─⟨ Γ⊢ ⟩
        Γ ⊢ Ψ n [ # n ]₀                  ─⟨ Wkn0 ⟩
        Ax n ∷ Γ ⊢ Ψ n [ # n ]₀
```

**<u>定理</u>** `𝒜ω` 是极大全称化的.  
**<u>证明</u>** 给定 `𝒜ω` 的任意扩张 `𝒯` 和任意公式 `φ`, 要证

目标: 如果对任意项 `t`, `φ [ t ]₀ ` 都是 `𝒯` 的定理, 那么 `∀̇ φ` 是 `𝒯` 的定理.

由于 `Ψ` 是公式的枚举函数, 所以存在 `n` 使得 `Ψ n ≡ φ`. 用 `Ψ n` 替换目标中的 `φ`, 再用 `# n` 实例化 `t`, 目标就变成了上一个引理的形式. ∎

```agda
  𝒜ω-isMaxAll : isMaxAll 𝒜ω
  𝒜ω-isMaxAll 𝒯 φ 𝒜ω⊆𝒯 H∀ = 𝟙.rec 𝟙.squash H (Ψ-wit φ) where
    H : Σ n ， Ψ n ≡ φ → ∥ 𝒯 ⊢ᵀ (∀̇ φ) ∥₁
    H (n , refl) = 𝟙.map (𝒜ω-isMaxAll-Ψ 𝒯 𝒜ω⊆𝒯) (H∀ (# n))
```

## 极大一致扩张

极大一致扩张的输入是一个理论, 但不要求闭. 与上一小节同样地, 我们导入集合的添加元素操作 `_⨭_`.

```agda
module MaxConExtension (𝒯ⁱ : Theory) where
  open SetOperation (discreteSet {A = Formula})
```

**<u>定义</u>** 极大一致: 我们说 `𝒯` 极大一致, 当且仅当对 `𝒯` 的任意一致扩张 `𝒯 ⨭ φ`, `φ` 都已经在 `𝒯` 里了.

```agda
  isMaxCon : Theory → 𝕋
  isMaxCon 𝒯 = ∀ φ → Con (𝒯 ⨭ φ) to 𝒯 → φ ∈ 𝒯
```

**<u>引理</u>** 如果 `𝒯` 极大一致, 那么 `𝒯` 对证明封闭, 即能证的都已经在 `𝒯` 里了.
**<u>证明</u>** 只需证 `𝒯 ⊢ᵀ φ` 蕴含 `Con (𝒯 ⨭ φ) to 𝒯`, 即证 `𝒯 ⊢ᵀ φ → 𝒯 ⨭ φ ⊢ ⊥̇ → 𝒯 ⊢ ⊥̇`, 此即规则 `Cutᵀ`. ∎

```agda
  closed-under-⊢ : isMaxCon 𝒯 → 𝒯 ⊢ᵀ φ → φ ∈ 𝒯
  closed-under-⊢ {𝒯} {φ} max H = max _ $ 𝟙.map $ Cutᵀ {𝒯} φ H
```

**<u>定义</u>** 一致单集: `Con (𝒯 ⨭ φ) to 𝒯` 时为 `φ` 的单集, 否则为空集的集合叫做 `φ` 对 `𝒯` 的一致单集, 记作 `｛ φ ｝⟨ 𝒯 ⟩`.

```agda
  ｛_｝⟨_⟩ : Formula → Theory → Theory
  ｛ φ ｝⟨ 𝒯 ⟩ = λ ψ → φ ≡ ψ ∧ Con (𝒯 ⨭ φ) to 𝒯 , isProp× (discreteSet _ _) (isProp→ 𝟙.squash)
```

**<u>定义</u>** 一致添加: `𝒯` 与 `｛ φ ｝⟨ 𝒯 ⟩` 的二元并叫做 `𝒯` 一致添加 `φ`, 记作 `𝒯 ⨭ᶜ φ`.

```agda
  _⨭ᶜ_ : Theory → Formula → Theory
  𝒯 ⨭ᶜ φ = 𝒯 ∪ ｛ φ ｝⟨ 𝒯 ⟩
```

## 完备扩张的构造

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/TheoryExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.TheoryExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.extension)  
> 交流Q群: 893531731
