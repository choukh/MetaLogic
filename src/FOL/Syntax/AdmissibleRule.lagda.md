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
**<u>证明</u>** 对证明树归纳. 除 `AllI` 和 `AllE` 之外的情况的证明与 `Wkn` 类似.

```agda
SubstWkn : (σ : Subst) → Γ ⊢ φ → map _[ σ ]ᵩ Γ ⊢ φ [ σ ]ᵩ
SubstWkn σ (Ctx H) = Ctx (∈map-intro H refl)
SubstWkn σ (ImpI H) = ImpI (SubstWkn σ H)
SubstWkn σ (ImpE H₁ H₂) = ImpE (SubstWkn σ H₁) (SubstWkn σ H₂)
SubstWkn σ (FalseE H) = FalseE (SubstWkn σ H)
SubstWkn σ (Peirce φ ψ) = Peirce (φ [ σ ]ᵩ) (ψ [ σ ]ᵩ)
```

对于 `AllI` 的情况, 要证 `map (_[ σ ]ᵩ) Γ ⊢ (∀̇ φ) [ σ ]ᵩ`.
有归纳假设 `map (_[ ↑ₛ σ ]ᵩ) (↑ Γ) ⊢ φ [ ↑ₛ σ ]ᵩ`.
对目标使用 `AllI` 归纳, 只要证 `↑ (map (_[ σ ]ᵩ) Γ) ⊢ φ [ ↑ₛ σ ]ᵩ`.
将目标 `⊢` 式的左边换成 `map (_[ ↑ₛ σ ]ᵩ) (↑ Γ)` 即证. ∎

```agda
SubstWkn {Γ} σ (AllI H) = AllI $ subst (_⊢ _) ↑∘[] (SubstWkn (↑ₛ σ) H)
```

对于 `AllE` 的情况, 要证 `map (_[ σ ]ᵩ) Γ ⊢ (φ [ t ]₀) [ σ ]ᵩ`.
有归纳假设 `map (_[ σ ]ᵩ) Γ ⊢ (∀̇ φ) [ σ ]ᵩ`.
对归纳假设使用 `AllE` 规则, 可得对任意 `t` 有 `map (_[ σ ]ᵩ) Γ ⊢ (φ [ ↑ₛ σ ]ᵩ) [ t ]₀`.
将目标 `⊢` 式的右边可以换成 `(φ [ ↑ₛ σ ]ᵩ) [ t [ σ ]ₜ ]₀` 即证.

```agda
SubstWkn σ (AllE H) = subst (_ ⊢_) ([]ᵩ∘[]₀ _) (AllE (SubstWkn σ H))
```

## 局部无名

借助“未使用变元”的概念, 我们可以表述所谓**局部无名 (locally nameless)** 变换, 并且利用替换弱化规则, 我们可以证明它.

**<u>引理</u>** 局部无名变换: 如果 `n` 在 `Γ` 以及 `∀̇ φ` 中未使用, 那么 `↑ Γ ⊢ φ` 与 `Γ ⊢ φ [ # n ]₀` 逻辑等价.  
**<u>证明</u>**

```agda
nameless-conversion : fresh n Γ → freshᵩ n (∀̇ φ) → ↑ Γ ⊢ φ ↔ Γ ⊢ φ [ # n ]₀
nameless-conversion {n} {Γ} freshΓ fresh∀̇φ =
  ⇒: (λ ↑Γ⊢φ   → subst (_⊢ _) eq (SubstWkn (# n ∷ₙ #) ↑Γ⊢φ))
  ⇐: (λ Γ⊢φ[n] → {!   !})
  where
  eq = Γ                         ≡˘⟨ map-id Γ ⟩
    map id Γ                     ≡˘⟨ map-ext (λ _ _ → ↑ᵩ[]₀) ⟩
    map (_[ # n ∷ₙ # ]ᵩ ∘ ↑ᵩ) Γ  ≡⟨ map-∘ Γ ⟩
    map (_[ # n ∷ₙ # ]ᵩ) (↑ Γ)   ∎
  -- switch binder to n
  -- k   = 0 1 2 3 4 5 6 ...
  -- ζ 4 = 1 2 3 4 0 6 7 ...
  ζ : ℕ → Subst
  ζ n = λ k → if does (n ≟ k) then # 0 else # (suc k)
  -- k        = 0 1 2 3 | 4
  -- [ ζ 4 ]ᵩ = 1 2 3 4 | 0
  ζ-lift : ∀ n → freshᵩ n φ → φ [ ζ n ]ᵩ ≡ ↑ᵩ φ
  ζ-lift n H = {!   !}
  -- k                 = 0 1 2 3 | 4
  -- [ # 3 ]₀          = 3 0 1 2 | 4
  -- [ # 3 ]₀ [ ζ 3 ]ᵩ = 0 1 2 3 | 4
  ζ-id : ∀ n → freshᵩ (suc n) φ → φ [ # n ]₀ [ ζ n ]ᵩ ≡ φ
  ζ-id n H = {!   !}
```

**<u>引理</u>** 局部无名规则: 如果 `n` 在 `Γ` 以及 `∀̇ φ` 中未使用, 那么 `Γ ⊢ φ [ # n ]₀` 蕴含 `Γ ⊢ ∀̇ φ`.  
**<u>证明</u>** 由局部无名变换及 `AllI` 即得. ∎

```agda
AllI′ : fresh n Γ → freshᵩ n (∀̇ φ) → Γ ⊢ φ [ # n ]₀ → Γ ⊢ ∀̇ φ
AllI′ freshΓ fresh∀̇φ = AllI ∘ nameless-conversion freshΓ fresh∀̇φ .⇐
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/AdmissibleRule.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.AdmissibleRule.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.admissible)  
> 交流Q群: 893531731
