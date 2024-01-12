---
url: fol.henkin
---

# 一阶逻辑 ▸ 亨金扩张

亨金扩张是指一种扩张理论的方法, 也可以指用该方法扩张后的理论. 亨金扩张的目的是使扩张后的理论满足一定的性质, 以证明一阶逻辑的完备性, 这会在下一篇讲解. 本篇先介绍亨金扩张所具有的性质, 然后讲解扩张的方法.

```agda
open import Foundation.Essential
open import Foundation.Data.Nat.Order

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
      𝒯ᵒ-consistent : Con 𝒯ᵒ to 𝒯ⁱ
      𝒯ᵒ-extension : 𝒯ⁱ ⊆ 𝒯ᵒ
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
  (𝒯ᵢ-consistent : ∀ n → Con 𝒯ᵢ (suc n) to 𝒯ᵢ n)
  (𝒯ᵢ-extension : ∀ m n → m ≤ n → 𝒯ᵢ m ⊆ 𝒯ᵢ n)
  where
```

**<u>定义</u>** 无穷扩张的所有步骤所得到的理论的并, 叫做无穷扩张的极限.

```agda
  limit : Theory
  limit = ⋃ᵢ 𝒯ᵢ
```

**<u>引理</u>** 如果无穷扩张的极限可证 `φ`, 那么必然存在其中一步理论可证 `φ`.  

```agda
  limit-⊩ : ∀ φ → limit ⊩ φ → ∃ n ， 𝒯ᵢ n ⊩ φ
  limit-⊩ φ (Γ , Γ⊆l , Γ⊢φ) = 𝟙.map (λ { (n , Γ⊆𝒯ᵢ) → n , Γ , Γ⊆𝒯ᵢ , Γ⊢φ }) (aux Γ Γ⊆l) where
    aux : ∀ Γ → Γ ᴸ⊆ᴾ limit → ∃ n ， Γ ᴸ⊆ᴾ 𝒯ᵢ n
    aux [] _ = ex 0 λ _ ()
    aux (φ ∷ Γ) Γ⊆l = {!   !}
```

### Herbelin-Ilik扩张

### 极大一致扩张

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/HenkinExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.HenkinExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.henkin)  
> 交流Q群: 893531731
