---
url: fol.syntax.admissible
---

# 一阶逻辑 ▸ 语法 ▸ 可容许规则


若在一个形式系统中添加一个推理规则后, 该系统的定理集合不发生变化, 则称该推理规则在该形式系统中是**可容许的 (admissible)**. 换句话说, 使用该规则可证明的每个公式在没有该规则的情况下已经是可证明的. 因此在某种程度上说, 该规则是冗余的. 但是对于研究这个系统而言, 它们是重要引理.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.AdmissibleRule (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
open import FOL.Syntax.SubstitutionFacts ℒ

private variable
  n : ℕ
```

## 弱化

弱化指的是对语境的弱化. 此类规则允许我们通过在弱化的语境中证明某公式, 来说明原语境中就能证明该公式.

**<u>引理</u>** 弱化规则: `Γ ⊆ᴸ Δ` 蕴含 `Γ ⊢ φ → Δ ⊢ φ`.
**<u>证明</u>** 对证明树归纳即得. ∎

```agda
Wkn : Γ ⊆ᴸ Δ → Γ ⊢ φ → Δ ⊢ φ
Wkn sub (Ctx H) = Ctx (sub H)
Wkn sub (ImpI H) = ImpI (Wkn (∷⊆∷ sub) H)
Wkn sub (ImpE H₁ H₂) = ImpE (Wkn sub H₁) (Wkn sub H₂)
Wkn sub (AllI H) = AllI (Wkn (map⊆map sub) H)
Wkn sub (AllE H) = AllE (Wkn sub H)
Wkn sub (FalseE H) = FalseE (Wkn sub H)
Wkn sub (Peirce φ ψ) = Peirce φ ψ
```

**<u>引理</u>** 替换弱化规则: 一个证明在其语境和结论同时做同种替换后仍然有效.  
**<u>证明</u>** 对证明树归纳, 我们只讲 `AllI` 和 `AllE` 的情况, 其他情况的证明与 `Wkn` 类似.

```agda
SubstWkn : (σ : Subst) → Γ ⊢ φ → map _[ σ ]ᵩ Γ ⊢ φ [ σ ]ᵩ
SubstWkn σ (Ctx H) = Ctx (∈map-intro H refl)
SubstWkn σ (ImpI H) = ImpI (SubstWkn σ H)
SubstWkn σ (ImpE H₁ H₂) = ImpE (SubstWkn σ H₁) (SubstWkn σ H₂)
SubstWkn σ (FalseE H) = FalseE (SubstWkn σ H)
SubstWkn σ (Peirce φ ψ) = Peirce (φ [ σ ]ᵩ) (ψ [ σ ]ᵩ)
```

```agda
SubstWkn σ (AllE H) = subst (_ ⊢_) ([]ᵩ-∘-[]₀ _) (AllE (SubstWkn σ H))
```

```agda
SubstWkn {Γ} σ (AllI H) = AllI $ subst (_⊢ _) eq (SubstWkn (↑ₛ σ) H) where
  eq = ↑ (map (_[ σ ]ᵩ) Γ)      ≡˘⟨ map-∘ Γ ⟩
       map (↑ᵩ ∘ _[ σ ]ᵩ) Γ     ≡⟨ map-ext (λ t _ → ↑ᵩ-∘-[]ᵩ σ t) ⟩
       map (_[ ↑ₛ σ ]ᵩ ∘ ↑ᵩ) Γ  ≡⟨ map-∘ Γ ⟩
       map (_[ ↑ₛ σ ]ᵩ) (↑ Γ)   ∎
```

## 局部无名

借助新变元的概念, 我们可以表述关于全称量词的所谓**局部无名 (locally nameless)** 规则 `AllI′`.

```agda
AllI′ : fresh n Γ → freshᵩ n (∀̇ φ) → Γ ⊢ φ [ # n ]₀ → Γ ⊢ ∀̇ φ
AllI′ freshΓ fresh∀̇φ Γ⊢φ[n] = AllI {!   !}
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/AdmissibleRule.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.AdmissibleRule.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.admissible)  
> 交流Q群: 893531731
