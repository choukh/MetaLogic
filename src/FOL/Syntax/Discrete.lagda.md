---
url: fol.syntax.discrete
---

# 一阶逻辑 ▸ 语法 ▸ 公式的离散性

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.Discrete (ℒ : Language) where

open import FOL.Syntax.Base ℒ
instance _ = ℒ
```

```agda
f$̇-inj : {f : 𝓕} {t⃗ s⃗ : 𝕍 Term ∣ f ∣ᶠ} → f $̇ t⃗ ≡ f $̇ s⃗ → t⃗ ≡ s⃗
f$̇-inj {f} {t⃗} {s⃗} eq = ,-injʳ discreteSet eqΣ where
  toΣ : Term → Σ n ， 𝕍 Term n
  toΣ (# n) = 0 , []
  toΣ (f $̇ t⃗) = ∣ f ∣ᶠ , t⃗
  eqΣ : (∣ f ∣ᶠ , t⃗) ≡ (∣ f ∣ᶠ , s⃗)
  eqΣ = cong toΣ eq
```

```agda
R$̇-inj : {R : 𝓡} {t⃗ s⃗ : 𝕍 Term ∣ R ∣ᴿ} → R $̇ t⃗ ≡ R $̇ s⃗ → t⃗ ≡ s⃗
R$̇-inj {R} {t⃗} {s⃗} eq = ,-injʳ discreteSet eqΣ where
  toΣ : Formula → Σ n ， 𝕍 Term n
  toΣ ⊥̇ = 0 , []
  toΣ (_ →̇ _) = 0 , []
  toΣ (∀̇ _) = 0 , []
  toΣ (R $̇ t⃗) = ∣ R ∣ᴿ , t⃗
  eqΣ : (∣ R ∣ᴿ , t⃗) ≡ (∣ R ∣ᴿ , s⃗)
  eqΣ = cong toΣ eq
```

```agda
instance
  discrTerm : discrete Term
  discrTerm = term-elim {P = λ t → ∀ s → Dec (t ≡ s)} H# H$̇ _ _ where
    H# : (m : ℕ) (s : Term) → Dec (# m ≡ s)
    H# m (# n) with m ≟ n
    ... | yes refl = yes refl
    ... | no ¬eq = no λ { refl → ¬eq refl }
    H# m (f $̇ t⃗) = no λ ()
    H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → ∀ s → Dec (t ≡ s)) → ∀ s → Dec ((f $̇ t⃗) ≡ s)
    H$̇ f t⃗ IH (# n) = no λ ()
    H$̇ f t⃗ IH (g $̇ s⃗) with f ≟ g
    ... | no ¬eq = no λ { refl → ¬eq refl }
    ... | yes refl with discrete𝕍-strong t⃗ s⃗ IH
    ... | yes refl = yes refl
    ... | no ¬eq = no λ eq → ¬eq $ f$̇-inj eq
```

```agda
  discrFormula : discrete Formula
  discrFormula = H _ _ where
    H : ∀ φ ψ → Dec (φ ≡ ψ)
    H ⊥̇ ⊥̇ = yes refl
    H ⊥̇ (_ →̇ _) = no λ ()
    H ⊥̇ (∀̇ _) = no λ ()
    H ⊥̇ (_ $̇ _) = no λ ()
    H (φ₁ →̇ ψ₁) ⊥̇ = no λ ()
    H (φ₁ →̇ ψ₁) (φ₂ →̇ ψ₂) with H φ₁ φ₂ | H ψ₁ ψ₂
    ... | yes refl | yes refl = yes refl
    ... | no ¬eq   | _        = no λ { refl → ¬eq refl }
    ... | _        | no ¬eq   = no λ { refl → ¬eq refl }
    H (φ₁ →̇ ψ₁) (∀̇ _) = no λ ()
    H (φ₁ →̇ ψ₁) (_ $̇ _) = no λ ()
    H (∀̇ φ) ⊥̇ = no λ ()
    H (∀̇ φ) (_ →̇ _) = no λ ()
    H (∀̇ φ) (∀̇ ψ) with H φ ψ
    ... | yes refl = yes refl
    ... | no ¬eq   = no λ { refl → ¬eq refl }
    H (∀̇ φ) (_ $̇ _) = no λ ()
    H (R $̇ t⃗) ⊥̇ = no λ ()
    H (R $̇ t⃗) (_ →̇ _) = no λ ()
    H (R $̇ t⃗) (∀̇ _) = no λ ()
    H (R $̇ t⃗) (S $̇ s⃗) with R ≟ S
    ... | no ¬eq = no λ { refl → ¬eq refl }
    ... | yes refl with t⃗ ≟ s⃗
    ... | yes refl = yes refl
    ... | no ¬eq = no λ eq → ¬eq $ R$̇-inj eq
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Discrete.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Discrete.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.discrete)  
> 交流Q群: 893531731
