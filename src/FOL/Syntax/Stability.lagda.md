---
url: fol.syntax.stability
---

# 一阶逻辑 ▸ 语法 ▸ 稳定性

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.ReverseMaths

open import FOL.Language.Base
module FOL.Syntax.Stability (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.Discrete ℒ
open import FOL.Syntax.AdmissibleRules ℒ
open import FOL.Soundness ℒ
```

## 𝐓-稳定性

```agda
Theories : 𝕋₁
Theories = 𝒫⁻ Theory
```

```agda
⟨_⟩-stability : Theories → 𝕋₁
⟨ 𝐓 ⟩-stability = ∀ {𝒯 φ} → 𝒯 ∈⁻ 𝐓 → stable₁ (𝒯 ⊩ φ)
```

```agda
enclose : ℙ₀ → Theory
enclose 𝗣 φ = φ ≡ ⊥̇ ∧ 𝗣 holds , isProp× (discreteSet _ _) (isPredHolds 𝗣)
```

```agda
enclose↔ : ∀ 𝗣 → ∥ enclose 𝗣 ⊩ ⊥̇ ∥₁ ↔ 𝗣 holds
enclose↔ 𝗣 .⇒ = 𝟙.rec (isPredHolds 𝗣)
  λ { ([] , Γ⊆ , Γ⊢) → exfalso (consistency Γ⊢)
    ; (φ ∷ Γ , Γ⊆ , Γ⊢) → Γ⊆ (here refl) .snd }
enclose↔ 𝗣 .⇐ p = ∣_∣₁ $ [ ⊥̇ ] , (λ { (here refl) → refl , p }) , Ctx0
```

## 𝐔-稳定性

```agda
𝐔 : Theories
𝐔 = λ _ → ⊤ₚ*
```

```agda
𝗗𝗡𝗘↔𝐔-stability : 𝗗𝗡𝗘 ↔ ⟨ 𝐔 ⟩-stability
𝗗𝗡𝗘↔𝐔-stability .⇒ dne _ = 𝗗𝗡𝗘↔𝗗𝗡𝗘₁ .⇒ dne _
𝗗𝗡𝗘↔𝐔-stability .⇐ u-stb P propP = stable-subst (enclose↔ (P , propP)) $ stableInhabitation .⇒ $ u-stb _
```

## 𝐅-稳定性

```agda
𝐅 : Theories
𝐅 = λ 𝒯 → ∃ₚ Γ ， ∀ φ → φ ∈ 𝒯 ↔ φ ∈ᴸ Γ
```

```agda
theory : Context → Theory
theory Γ = λ φ → ∥ φ ∈ᴸ Γ ∥ₚ
```

```agda
theory↔ : theory Γ ⊩₁ φ ↔ Γ ⊢₁ φ
theory↔ .⇒ = 𝟙.rec→1 λ { (Δ , Δ⊆ , Δ⊢) → Wkn₁ Δ⊆ Δ⊢ }
theory↔ .⇐ = 𝟙.map λ Γ⊢ → _ , ∣_∣₁ , Γ⊢
```

## 𝐄-稳定性

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Stability.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Stability.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.stability)  
> 交流Q群: 893531731
