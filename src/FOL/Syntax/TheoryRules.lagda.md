---
url: fol.syntax.theory
---

# 一阶逻辑 ▸ 语法 ▸⁻ 理论规则

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.Relation.Nullary.Discrete.List

open import FOL.Language.Base
module FOL.Syntax.TheoryRules (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.Discrete ℒ
open import FOL.Syntax.AdmissibleRules ℒ
open SetOperation (discreteSet {A = Formula})
```

## 不规则转换

**<u>规则</u>** `Ctx` 的理论版.

```agda
Ctxᵀ : φ ∈ 𝒯 → 𝒯 ⊩ φ
Ctxᵀ {φ} φ∈𝒯 = [ φ ] , (λ { (here refl) → φ∈𝒯 }) , Ctx0
```

**<u>规则</u>** `ImpI` 的理论版.

```agda
ImpIᵀ : (𝒯 ⨭ φ) ⊩ ψ → 𝒯 ⊩ φ →̇ ψ
ImpIᵀ {𝒯} {φ} (Γ , Γ⊆𝒯⨭φ , Γ⊢) = Γ ∖[ φ ] , H₁ , ImpI (Wkn H₂ Γ⊢) where
  H₁ : Γ ∖[ φ ] ⊆̣͆ 𝒯
  H₁ {x} x∈ with ∈∖[]-elim x∈
  ... | x∈Γ , x≢φ = 𝟙.rec isProp∈ H (Γ⊆𝒯⨭φ x∈Γ) where
    H : x ∈ 𝒯 ⊎ x ∈ ｛ φ ｝ → x ∈ 𝒯
    H (inj₁ p) = p
    H (inj₂ refl) = exfalso (x≢φ refl)
  H₂ : Γ ⊆͆ φ ∷ Γ ∖[ φ ]
  H₂ = ⊆͆-trans {j = φ ∷ Γ} there ∷⊆∷∖[]
```

**<u>规则</u>** `ImpE` 的理论版.

```agda
ImpEᵀ : 𝒯 ⊩ φ →̇ ψ → 𝒯 ⊩ φ → 𝒯 ⊩ ψ
ImpEᵀ {𝒯} (Γ , Γ⊆ , Γ⊢) (Δ , Δ⊆ , Δ⊢) = Γ ++ Δ , sub , ImpE (Wkn (⊆++ˡ _ _) Γ⊢) (Wkn (⊆++ʳ _ _) Δ⊢) where
  sub : Γ ++ Δ ⊆̣͆ 𝒯
  sub ∈++ with ∈++-elim Γ ∈++
  ... | inj₁ ∈Γ = Γ⊆ ∈Γ
  ... | inj₂ ∈Δ = Δ⊆ ∈Δ
```

**<u>规则</u>** `Cut` 的理论版.

```agda
Cutᵀ : ∀ φ → 𝒯 ⊩ φ → 𝒯 ⨭ φ ⊩ ψ → 𝒯 ⊩ ψ
Cutᵀ _ H₁ H₂ = ImpEᵀ (ImpIᵀ H₂) H₁
```

**<u>规则</u>** `Wkn` 的理论版.

```agda
Wknᵀ : ∀ 𝒯₁ 𝒯₂ → 𝒯₁ ⊆ 𝒯₂ → 𝒯₁ ⊩ φ → 𝒯₂ ⊩ φ
Wknᵀ _ _ 𝒯₁⊆𝒯₂ (Γ , Γ⊆𝒯₁ , Γ⊢) = Γ , 𝒯₁⊆𝒯₂ ∘ Γ⊆𝒯₁ , Γ⊢
```

**<u>事实</u>** 相对一致的继承性: 如果 `𝒯₂` 与 `𝒯₃` 相对一致, 那么 `𝒯₂` 的子集 `𝒯₁` 与 `𝒯₃` 的亲集 `𝒯₄` 相对一致.  
**<u>证明</u>** 用 `Wknᵀ` 即得. ∎

```agda
Con-inherit : ∀ {𝒯₁ 𝒯₂ 𝒯₃ 𝒯₄} → 𝒯₁ ⊆ 𝒯₂ → 𝒯₃ ⊆ 𝒯₄ → Con 𝒯₂ to 𝒯₃ → Con 𝒯₁ to 𝒯₄
Con-inherit {𝒯₁} {𝒯₂} {𝒯₃} {𝒯₄} 𝒯₁⊆𝒯₂ 𝒯₃⊆𝒯₄ con =
  𝟙.map (Wknᵀ 𝒯₃ 𝒯₄ 𝒯₃⊆𝒯₄) ∘ con ∘ 𝟙.map (Wknᵀ 𝒯₁ 𝒯₂ 𝒯₁⊆𝒯₂)
```

## 规则转换

```agda
tauto : ◌⊢ φ → ◌⊩ φ
tauto H = [] , (λ ()) , H

rule : (∀ {Γ} → Γ ⊢ φ → Γ ⊢ ψ) → ∀ {𝒯} → 𝒯 ⊩ φ → 𝒯 ⊩ ψ
rule H = ImpEᵀ $ tauto $ ImpI′ H
```

**<u>规则</u>** `Contra` 的理论版.

```agda
Contraᵀ : 𝒯 ⨭ ¬̇ φ ⊩ ⊥̇ → 𝒯 ⊩ φ
Contraᵀ {𝒯} {φ} H = ImpEᵀ H₁ H₂ where
  H₁ =                  ∅─⟨ tauto (Peirce φ ⊥̇) ⟩
    𝒯 ⊩ (¬̇ φ →̇ φ) →̇ φ
  H₂ =                  ∅─⟨ H ⟩
    𝒯 ⨭ ¬̇ φ ⊩ ⊥̇        ─⟨ rule FalseE ⟩
    𝒯 ⨭ ¬̇ φ ⊩ φ        ─⟨ ImpIᵀ ⟩
    𝒯 ⊩ ¬̇ φ →̇ φ
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/TheoryRules.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.TheoryRules.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.theory)  
> 交流Q群: 893531731
