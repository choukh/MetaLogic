---
url: fol.syntax
---

# 一阶逻辑: 语法

```agda
open import FOL.Language
module FOL.Syntax (ℒ : Language) where

open import Foundation.Essential
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)
open import Foundation.Data.Vec.SetTheoretic
  renaming (_∈_ to _∈⃗_)

open Language ℒ

infix 10 _⊢_ _⊬_ _⊩_ _⊮_
infixl 15 _→̇_
infix 30 _[_]ₜ _[_]ₜ⃗ _[_]ᵩ

data Term : 𝕋 where
  #_ : ℕ → Term
  _$̇_ : (f : 𝓕) → 𝕍 Term ∣ f ∣ᶠ → Term

Subst : 𝕋
Subst = ℕ → Term

_[_]ₜ : Term → Subst → Term
_[_]ₜ⃗ : ∀ {n} → 𝕍 Term n → Subst → 𝕍 Term n

(# n)   [ σ ]ₜ = σ n
(f $̇ t⃗) [ σ ]ₜ = f $̇ t⃗ [ σ ]ₜ⃗

[] [ σ ]ₜ⃗ = []
(t ∷ t⃗) [ σ ]ₜ⃗ = t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗

↑ₜ : Term → Term
↑ₜ = _[ #_ ∘ suc ]ₜ

↑ₜ⃗ : ∀ {n} → 𝕍 Term n → 𝕍 Term n
↑ₜ⃗ = _[ #_ ∘ suc ]ₜ⃗

[]ₜ⃗≡map⃗ : ∀ {n} (t⃗ : 𝕍 Term n) σ → t⃗ [ σ ]ₜ⃗ ≡ map⃗ (_[ σ ]ₜ) t⃗
[]ₜ⃗≡map⃗ [] σ = refl
[]ₜ⃗≡map⃗ (_ ∷ t⃗) σ = cong (_ ∷_) $ []ₜ⃗≡map⃗ t⃗ σ

data Formula : 𝕋 where
  ⊥̇ : Formula
  _$̇_ : (R : 𝓡) → 𝕍 Term ∣ R ∣ᴿ → Formula
  _→̇_ : Formula → Formula → Formula
  ∀̇_ : Formula → Formula

_[_]ᵩ : Formula → Subst → Formula
⊥̇       [ σ ]ᵩ = ⊥̇
(R $̇ t⃗) [ σ ]ᵩ = R $̇ map⃗ (_[ σ ]ₜ) t⃗
(φ →̇ ψ) [ σ ]ᵩ = φ [ σ ]ᵩ →̇ ψ [ σ ]ᵩ
(∀̇ φ)   [ σ ]ᵩ = ∀̇ φ [ # 0 ∷ₛ ↑ₜ ∘ σ ]ᵩ

↑ᵩ : Formula → Formula
↑ᵩ = _[ #_ ∘ suc ]ᵩ

_[_∷] : Formula → Term → Formula
φ [ t ∷] = φ [ t ∷ₛ #_ ]ᵩ

Context : 𝕋
Context = 𝕃 Formula

Theory : 𝕋₁
Theory = 𝒫 Formula

↑ : Context → Context
↑ = map ↑ᵩ

variable
  t : Term
  φ ψ : Formula
  Γ : Context
  𝒯 : Theory

data _⊢_ : Context → Formula → 𝕋 where
  Ctx     : φ ∈ᴸ Γ             → Γ ⊢ φ
  ImpI    : (φ ∷ Γ) ⊢ ψ       → Γ ⊢ φ →̇ ψ
  ImpE    : Γ ⊢ φ →̇ ψ → Γ ⊢ φ → Γ ⊢ ψ
  AllI    : ↑ Γ ⊢ φ           → Γ ⊢ ∀̇ φ
  AllE    : Γ ⊢ ∀̇ φ           → Γ ⊢ φ [ t ∷]
  FalseE  : Γ ⊢ ⊥̇             → Γ ⊢ φ
  Peirce  : ∀ φ ψ → Γ ⊢ ((φ →̇ ψ) →̇ φ) →̇ φ

_⊬_ : Context → Formula → 𝕋
Γ ⊬ φ = ¬ (Γ ⊢ φ)

_⊩_ : Theory → Formula → 𝕋
𝒯 ⊩ φ = Σ _ λ Γ → (∀ φ → φ ∈ᴸ Γ → φ ∈ 𝒯) → Γ ⊢ φ

_⊮_ : Theory → Formula → 𝕋
𝒯 ⊮ φ = ¬ (𝒯 ⊩ φ)
```

> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax)  
> 交流Q群: 893531731
