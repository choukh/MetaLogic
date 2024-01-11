---
url: fol.henkin
---

# 一阶逻辑 ▸ 亨金扩张

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.HenkinExtension (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
```

## 亨金扩张的输入和输出

```agda
record Input : 𝕋₁ where
  field
    𝒯ⁱ : Theory
    𝒯ⁱ-closed : ∀ φ → φ ∈ 𝒯ⁱ → closed φ
```

```agda
record Output (input : Input) : 𝕋₁ where
  open Input input
  field
    𝒯ᵒ : Theory
    𝒯ᵒ-consistent : Con 𝒯ᵒ to 𝒯ⁱ
    𝒯ᵒ-extension : 𝒯ⁱ ⊆ 𝒯ᵒ

    𝒯ᵒ-closed-under-⊩ : ∀ φ → 𝒯ᵒ ⊩ φ → φ ∈ 𝒯ᵒ
    𝒯ᵒ-distrib-over-→̇ : ∀ φ ψ → φ →̇ ψ ∈ 𝒯ᵒ ↔ (φ ∈ 𝒯ᵒ → ψ ∈ 𝒯ᵒ)
    𝒯ᵒ-distrib-over-∀̇ : ∀ φ → ∀̇ φ ∈ 𝒯ᵒ ↔ ∀ t → φ [ t ∷] ∈ 𝒯ᵒ
```

## 亨金扩张的构造

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/HenkinExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.HenkinExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.henkin)  
> 交流Q群: 893531731
