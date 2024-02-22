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
Theories = 𝒫̅ Theory
```

```agda
⟨_⟩-stability : Theories → 𝕋₁
⟨ 𝐓 ⟩-stability = ∀ {𝒯 φ} → 𝒯 ∈̅ 𝐓 → stable₁ (𝒯 ⊩ φ)
```

## 𝐔-稳定性

```agda
𝐔 : Theories
𝐔 = λ _ → ⊤ₚ*
```

```agda
enclose : 𝕋 → Theory
enclose A φ = φ ≡ ⊥̇ ∧ inhabited A , isProp× (discreteSet _ _) 𝟙.squash
```

`A` 的居留性等价于 `enclose A` 的不一致性.

```agda
enclose↔ : enclose A ⊩₁ ⊥̇ ↔ inhabited A
enclose↔ .⇒ = 𝟙.rec→1
  λ { ([] , Γ⊆ , Γ⊢) → exfalso (consistency Γ⊢)
    ; (φ ∷ Γ , Γ⊆ , Γ⊢) → Γ⊆ (here refl) .snd }
enclose↔ .⇐ p = ∣_∣₁ $ [ ⊥̇ ] , (λ { (here refl) → refl , p }) , Ctx0
```

```agda
𝐔stb↔𝗗𝗡𝗘₁ : ⟨ 𝐔 ⟩-stability ↔ 𝗗𝗡𝗘₁
𝐔stb↔𝗗𝗡𝗘₁ .⇒ u-stb _ = stable₁-subst enclose↔ (u-stb _)
𝐔stb↔𝗗𝗡𝗘₁ .⇐ dne _ = dne _
```

𝐔-稳定性等价于排中律.

```agda
𝐔stb↔𝗟𝗘𝗠 : ⟨ 𝐔 ⟩-stability ↔ 𝗟𝗘𝗠
𝐔stb↔𝗟𝗘𝗠 = ⟨ 𝐔 ⟩-stability ↔⟨ 𝐔stb↔𝗗𝗡𝗘₁ ⟩
           𝗗𝗡𝗘₁            ↔˘⟨ 𝗗𝗡𝗘↔𝗗𝗡𝗘₁ ⟩
           𝗗𝗡𝗘             ↔˘⟨ 𝗟𝗘𝗠↔𝗗𝗡𝗘 ⟩
           𝗟𝗘𝗠             ↔∎
```

## 𝐅-稳定性

```agda
𝐅 : Theories
𝐅 = λ 𝒯 → ∃ₚ Γ ， ∀ {φ} → φ ∈ 𝒯 ↔ φ ∈͆₁ Γ
```

```agda
setΓ∈𝐅 : set Γ ∈̅ 𝐅
setΓ∈𝐅 {Γ} = ∣ Γ , ↔-refl ∣₁
```

```agda
⊩↔⊢ : set Γ ⊩₁ φ ↔ Γ ⊢₁ φ
⊩↔⊢ .⇒ = 𝟙.rec→1 λ { (Δ , Δ⊆ , Δ⊢) → Wkn₁ Δ⊆ Δ⊢ }
⊩↔⊢ .⇐ = 𝟙.map λ Γ⊢ → _ , ∣_∣₁ , Γ⊢
```

```agda
∈𝐅-elim : 𝒯 ∈̅ 𝐅 → ∃ Γ ， 𝒯 ⊩₁ φ ↔ Γ ⊢₁ φ
∈𝐅-elim = 𝟙.map $ uncurry λ Γ iff → Γ ,
  ⇒: 𝟙.rec→1 (λ { (Δ , Δ⊆ , Δ⊢) → Wkn₁ (iff .⇒ ∘ Δ⊆) Δ⊢ })
  ⇐: 𝟙.map λ Γ⊢ → Γ , (λ ∈Γ → iff .⇐ ∣ ∈Γ ∣₁) , Γ⊢
```

𝐅-稳定性等价于语境可证的稳定性.

```agda
𝐅stb↔⊢stb : ⟨ 𝐅 ⟩-stability ↔ ∀ {Γ φ} → stable₁ (Γ ⊢ φ)
𝐅stb↔⊢stb .⇒ stb = stable₁-subst ⊩↔⊢ (stb setΓ∈𝐅)
𝐅stb↔⊢stb .⇐ stb 𝒯∈̅𝐅 = 𝟙.rec (isProp→ 𝟙.squash) (λ H → stable₁-subst (↔-sym $ H .snd) stb) (∈𝐅-elim 𝒯∈̅𝐅)
```

## 𝐄-稳定性

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Stability.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Stability.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.stability)  
> 交流Q群: 893531731
