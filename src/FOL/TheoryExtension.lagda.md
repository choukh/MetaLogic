---
url: fol.extension
---

# 一阶逻辑 ▸ 理论的扩张

理论扩张的目的是使扩张后的理论满足一定的性质, 以证明一阶逻辑的完备性, 这会在下一篇讲解. 本篇先介绍此种扩张 (以下称为完备化扩张) 应具有的性质, 然后讲解该扩张的具体构造.

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder

open import FOL.Language
module FOL.TheoryExtension (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.Discrete ℒ
open import FOL.Syntax.Enumeration ℒ
open import FOL.Syntax.FreshVariables ℒ
open import FOL.Syntax.AdmissibleRule ℒ

private variable
  m n : ℕ
  𝒯 : Theory
```

## 扩张的输入和输出

完备化扩张的输入要求是一个闭理论, 即由闭公式所组成的理论.

```agda
module _ ((𝒯ⁱ , 𝒯ⁱ-closed) : ClosedTheory) where
```

闭理论 `𝒯ⁱ` 的完备化扩张是一个理论 `𝒯ᵒ`, 满足

- `𝒯ᵒ` 是 `𝒯ⁱ` 的一致扩张, 即 `𝒯ᵒ` 包含 `𝒯ⁱ` 且 `𝒯ᵒ` 相对于 `𝒯ⁱ` 一致
- `𝒯ᵒ` 对证明封闭, 即 `𝒯ᵒ` 的任意可证的公式都是 `𝒯ᵒ` 的成员
- `𝒯ᵒ` 中的蕴含式满足分配性: `φ →̇ ψ` 是 `𝒯ᵒ` 的成员当且仅当 `φ` 是 `𝒯ᵒ` 的成员蕴含 `ψ` 是 `𝒯ᵒ` 的成员
- `𝒯ᵒ` 中的全称量化式满足分配性: `∀̇ φ` 是 `𝒯ᵒ` 的成员当且仅当对任意项 `t`, `φ [ t ]₀` 是 `𝒯ᵒ` 的成员

```agda
  record Output : 𝕋₁ where
    field
      𝒯ᵒ : Theory
      𝒯ᵒ-sub : 𝒯ⁱ ⊆ 𝒯ᵒ
      𝒯ᵒ-con : Con 𝒯ᵒ to 𝒯ⁱ
      𝒯ᵒ-closed-under-⊩ : ∀ φ → 𝒯ᵒ ⊩ φ → φ ∈ 𝒯ᵒ

      𝒯ᵒ-distrib-over-→̇ : ∀ φ ψ → φ →̇ ψ ∈ 𝒯ᵒ ↔ (φ ∈ 𝒯ᵒ → ψ ∈ 𝒯ᵒ)
      𝒯ᵒ-distrib-over-∀̇ : ∀ φ → ∀̇ φ ∈ 𝒯ᵒ ↔ ∀ t → φ [ t ]₀ ∈ 𝒯ᵒ
```

## 扩张的构造

完备化扩张其实不是一轮扩张, 而是由两轮扩张构成, 按顺序分别叫做

1. Henkin扩张
2. 极大一致扩张

它们可以抽象出一个共通的基础构造: 理论的无穷扩张. 我们先讲这个.

### 理论的无穷扩张

Henkin扩张和极大一致扩张都不是一步到位的, 而是需要可数无穷步, 每一步都是上一步的一致扩张, 这样的扩张叫做理论的无穷扩张.

**<u>定义</u>** 理论的无穷扩张是理论的一个无穷序列, 其中每一项都是上一项的一致扩张.

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
  𝒯≤-con (≤-step m≤n) 𝒯₊⊩⊥̇ = 𝒯≤-con m≤n (𝒯₊-con 𝒯₊⊩⊥̇)
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
**<u>证明</u>** 由 `_⊩_` 的定义和引理 `⊆𝒯ω→⊆𝒯ₙ` 即得. ∎

```agda
  𝒯ω⊩→𝒯ₙ⊩ : ∀ {φ} → 𝒯ω ⊩ φ → ∃ n ， 𝒯ᵢ n ⊩ φ
  𝒯ω⊩→𝒯ₙ⊩ (Γ , Γ⊆l , Γ⊢φ) = 𝟙.map (λ { (n , Γ⊆𝒯ᵢ) → n , Γ , Γ⊆𝒯ᵢ , Γ⊢φ }) (⊆𝒯ω→⊆𝒯ₙ Γ Γ⊆l)
```

**<u>引理</u>** 无穷扩张的极限相对于起始理论一致.  
**<u>证明</u>** 由引理 `𝒯ω⊩→𝒯ₙ⊩` 和 `𝒯≤-con` 即得. ∎

```agda
  𝒯ω-con : Con 𝒯ω to 𝒯ᵢ 0
  𝒯ω-con ∥𝒯ω⊩⊥̇∥₁ = 𝟙.intro ∥𝒯ω⊩⊥̇∥₁ λ 𝒯ω⊩⊥̇ →
    𝟙.intro (𝒯ω⊩→𝒯ₙ⊩ 𝒯ω⊩⊥̇) λ { (n , 𝒯ₙ⊩⊥̇) → 𝒯≤-con z≤n ∣ 𝒯ₙ⊩⊥̇ ∣₁ }
```

**<u>引理</u>** 如果每一步扩张都是闭理论, 那么极限是闭理论.  
**<u>证明</u>** 依定义即得. ∎

```agda
  𝒯ω-closed : (∀ n → closedTheory (𝒯ᵢ n)) → closedTheory 𝒯ω
  𝒯ω-closed H φ = 𝟙.rec (isPredClosed φ) λ { (m , φ∈𝒯ₘ) → H m φ φ∈𝒯ₘ }
```

### Henkin扩张

这里讲的Henkin扩张采用 [Herbelin和Ilik](https://pauillac.inria.fr/~herbelin/articles/godel-completeness-draft16.pdf) 对原版Henkin扩张的构造主义改良版本.

```agda
module HenkinExtension ((𝒯ⁱ , 𝒯ⁱ-closed) : ClosedTheory) where
  open SetOperation (discreteSet {A = Formula})

  isℋ : Theory → 𝕋₁
  isℋ 𝒯 = ∀ 𝒯′ φ → 𝒯 ⊆ 𝒯′ → (∀ t → ∥ 𝒯′ ⊩ φ [ t ]₀ ∥₁) → ∥ 𝒯′ ⊩ ∀̇ φ ∥₁

  Ax : ℕ → Formula
  Ax n = (Ψ n) [ # n ]₀ →̇ ∀̇ (Ψ n)

  ℋᵢ : ℕ → Theory
  ℋᵢ zero = 𝒯ⁱ
  ℋᵢ (suc n) = ℋᵢ n ⨭ Ax n

  ℋ₊-sub : ℋᵢ n ⊆ ℋᵢ (suc n)
  ℋ₊-sub {n} = ⊆⨭ (ℋᵢ n)

  ℋ₊-con : Con (ℋᵢ (suc n)) to (ℋᵢ n)
  ℋ₊-con = 𝟙.map ℋ₊-⊩⊥̇ where
    ℋ₊-⊩⊥̇ : ℋᵢ (suc n) ⊩ ⊥̇ → ℋᵢ n ⊩ ⊥̇
    ℋ₊-⊩⊥̇ (Γ , Γ⊆ℋ₊ , Γ⊢) = {!   !} where
      H1 : freshᵩ n (Ψ n)
      H1 = Ψ-fresh ≤-refl

  open GeneralizedExtension (mkGenExt ℋᵢ ℋ₊-sub ℋ₊-con) public
    renaming ( 𝒯ω to ℋω
             ; 𝒯ω-sub to ℋω-sub
             ; 𝒯ω-con to ℋω-con
             ; 𝒯ω-closed to ℋω-closed
             )

  ℋω-isℋ-Ψ : ∀ 𝒯 → ℋω ⊆ 𝒯 → 𝒯 ⊩ (Ψ n [ # n ]₀) → 𝒯 ⊩ (∀̇ (Ψ n))
  ℋω-isℋ-Ψ {n} 𝒯 ℋω⊆𝒯 (Γ , Γ⊆𝒯 , Γ⊢) = Ax n ∷ Γ , ∷⊆𝒯 , ∷⊢∀̇ where
    ∷⊆𝒯 : (Ax n ∷ Γ) ᴸ⊆ᴾ 𝒯
    ∷⊆𝒯 (here refl) = ℋω⊆𝒯 (ex (suc n) (inr refl))
    ∷⊆𝒯 (there φ∈Γ) = Γ⊆𝒯 φ∈Γ
    ∷⊢∀̇ : (Ax n ∷ Γ) ⊢ ∀̇ (Ψ n)
    ∷⊢∀̇ = ImpE (Ctx (here refl)) (Wkn there Γ⊢)

  ℋω-isℋ : isℋ ℋω
  ℋω-isℋ 𝒯 φ ℋω⊆𝒯 H∀ = 𝟙.rec 𝟙.squash H (Ψ-wit φ) where
    H : Σ n ， Ψ n ≡ φ → ∥ 𝒯 ⊩ (∀̇ φ) ∥₁
    H (n , refl) = 𝟙.map (ℋω-isℋ-Ψ 𝒯 ℋω⊆𝒯) (H∀ (# n))
```

### 极大一致扩张

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/TheoryExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.TheoryExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.extension)  
> 交流Q群: 893531731
