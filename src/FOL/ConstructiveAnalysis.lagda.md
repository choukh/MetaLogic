---
url: fol.analysis
---

# 一阶逻辑 ▸ 构造主义纯度分析

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.ConstructiveAnalysis (ℒ : Language) where

open import FOL.Syntax.Base ℒ
```

## 𝐓-稳定性

```agda
Theories : 𝕋₂
Theories = 𝒫 Theory

⟨_⟩-stability : Theories → 𝕋₁
⟨ 𝐓 ⟩-stability = ∀ 𝒯 φ → 𝒯 ∈ 𝐓 → stable₁ (𝒯 ⊩ φ)

𝐔 : Theories
𝐔 = λ _ → ⊤ₚ*
```

## 双重否定消去

```agda
DNE : 𝕋 (ℓ ⁺)
DNE {ℓ} = (P : 𝕋 ℓ) → stable₁ P
```

```agda
DNE↔𝐔-stability : DNE ↔ ⟨ 𝐔 ⟩-stability
DNE↔𝐔-stability .⇒ dne 𝒯 φ _ = dne (𝒯 ⊩ φ)
DNE↔𝐔-stability .⇐ = {!   !}
```

## 综合马尔可夫

## 对象马尔可夫

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/ConstructiveAnalysis.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.ConstructiveAnalysis.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.analysis)  
> 交流Q群: 893531731
