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
open import FOL.Semantics.Base ℒ
```

```agda
record Input : 𝕋₁ where
  field
    𝒯ⁱ : Theory
    𝒯ⁱ-closed : ∀ φ → 𝒯ⁱ φ holds → closed φ
```

```agda
record Output (input : Input) : 𝕋ω where
  open Input input
  field
    𝒯ᵒ : Theory
    𝒯ᵒ-consistent : 𝒯ᵒ ⊫ ⊥̇ → 𝒯ⁱ ⊫ ⊥̇
    𝒯ᵒ-extension : 𝒯ⁱ ⊆ 𝒯ᵒ

    𝒯ᵒ-closed-under-⊩ : ∀ φ → 𝒯ᵒ ⊩ φ → φ ∈ 𝒯ᵒ
    𝒯ᵒ-distributes-over-→̇ : ∀ φ ψ → φ →̇ ψ ∈ 𝒯ᵒ ↔ (φ ∈ 𝒯ᵒ → ψ ∈ 𝒯ᵒ)
    𝒯ᵒ-distributes-over-∀̇ : ∀ φ → ∀̇ φ ∈ 𝒯ᵒ ↔ ∀ t → φ [ t ∷] ∈ 𝒯ᵒ
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/HenkinExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.HenkinExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.henkin)  
> 交流Q群: 893531731
