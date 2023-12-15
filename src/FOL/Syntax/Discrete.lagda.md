---
url: fol.syntax.discrete
---

# 一阶逻辑 ▸ 语法 ▸ 公式的离散性

我们希望说明 `Formula` 是一个集合, 并且可以被枚举. 这些都需要先建立其离散性.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.Discrete (ℒ : Language) where

open import FOL.Syntax.Base ℒ
instance _ = ℒ
```

## 构造子的单射性

**<u>引理</u>** 

```agda
#-inj : {m n : ℕ} → # m ≡ # n → m ≡ n
#-inj refl = refl
```

```agda
f$̇-injˡ : ∀ {f g t⃗ s⃗} → f Term.$̇ t⃗ ≡ g $̇ s⃗ → f ≡ g
f$̇-injˡ refl = refl
```

```agda
f$̇-injʳ : ∀ {f t⃗ s⃗} → f $̇ t⃗ ≡ f $̇ s⃗ → t⃗ ≡ s⃗
f$̇-injʳ {f} {t⃗} {s⃗} eq = ,-injʳ discreteSet eqΣ where
  toΣ : Term → Σ n ， 𝕍 Term n
  toΣ (# n) = 0 , []
  toΣ (f $̇ t⃗) = ∣ f ∣ᶠ , t⃗
  eqΣ : (∣ f ∣ᶠ , t⃗) ≡ (∣ f ∣ᶠ , s⃗)
  eqΣ = cong toΣ eq
```

```agda
→̇-injˡ : ∀ {φ₁ ψ₁ φ₂ ψ₂} → φ₁ →̇ ψ₁ ≡ φ₂ →̇ ψ₂ → φ₁ ≡ φ₂
→̇-injˡ refl = refl
```

```agda
→̇-injʳ : ∀ {φ₁ ψ₁ φ₂ ψ₂} → φ₁ →̇ ψ₁ ≡ φ₂ →̇ ψ₂ → ψ₁ ≡ ψ₂
→̇-injʳ refl = refl
```

```agda
∀̇-inj : ∀ {φ₁ φ₂} → ∀̇ φ₁ ≡ ∀̇ φ₂ → φ₁ ≡ φ₂
∀̇-inj refl = refl
```

```agda
R$̇-injˡ : ∀ {R S t⃗ s⃗} → R Formula.$̇ t⃗ ≡ S $̇ s⃗ → R ≡ S
R$̇-injˡ refl = refl
```

```agda
R$̇-injʳ : {R : 𝓡} {t⃗ s⃗ : 𝕍 Term ∣ R ∣ᴿ} → R $̇ t⃗ ≡ R $̇ s⃗ → t⃗ ≡ s⃗
R$̇-injʳ {R} {t⃗} {s⃗} eq = ,-injʳ discreteSet eqΣ where
  toΣ : Formula → Σ n ， 𝕍 Term n
  toΣ ⊥̇ = 0 , []
  toΣ (_ →̇ _) = 0 , []
  toΣ (∀̇ _) = 0 , []
  toΣ (R $̇ t⃗) = ∣ R ∣ᴿ , t⃗
  eqΣ : (∣ R ∣ᴿ , t⃗) ≡ (∣ R ∣ᴿ , s⃗)
  eqΣ = cong toΣ eq
```

## 项和公式的离散性

```agda
instance
  discrTerm : discrete Term
  discrTerm = term-elim {P = λ t → ∀ s → Dec (t ≡ s)} H# H$̇ _ _ where
    H# : (m : ℕ) (s : Term) → Dec (# m ≡ s)
    H# m (# n) with m ≟ n
    ... | yes refl = yes refl
    ... | no ¬eq = no $ ¬eq ∘ #-inj
    H# m (f $̇ t⃗) = no λ ()
    H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → ∀ s → Dec (t ≡ s)) → ∀ s → Dec ((f $̇ t⃗) ≡ s)
    H$̇ f t⃗ IH (# n) = no λ ()
    H$̇ f t⃗ IH (g $̇ s⃗) with f ≟ g
    ... | no ¬eq = no $ ¬eq ∘ f$̇-injˡ
    ... | yes refl with discrete𝕍-strong t⃗ s⃗ IH
    ... | yes refl = yes refl
    ... | no ¬eq = no $ ¬eq ∘ f$̇-injʳ
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
    ... | no ¬eq   | _        = no $ ¬eq ∘ →̇-injˡ
    ... | _        | no ¬eq   = no $ ¬eq ∘ →̇-injʳ
    H (φ₁ →̇ ψ₁) (∀̇ _) = no λ ()
    H (φ₁ →̇ ψ₁) (_ $̇ _) = no λ ()
    H (∀̇ φ) ⊥̇ = no λ ()
    H (∀̇ φ) (_ →̇ _) = no λ ()
    H (∀̇ φ) (∀̇ ψ) with H φ ψ
    ... | yes refl = yes refl
    ... | no ¬eq   = no $ ¬eq ∘ ∀̇-inj
    H (∀̇ φ) (_ $̇ _) = no λ ()
    H (R $̇ t⃗) ⊥̇ = no λ ()
    H (R $̇ t⃗) (_ →̇ _) = no λ ()
    H (R $̇ t⃗) (∀̇ _) = no λ ()
    H (R $̇ t⃗) (S $̇ s⃗) with R ≟ S
    ... | no ¬eq = no $ ¬eq ∘ R$̇-injˡ
    ... | yes refl with t⃗ ≟ s⃗
    ... | yes refl = yes refl
    ... | no ¬eq = no $ ¬eq ∘ R$̇-injʳ
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Discrete.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Discrete.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.discrete)  
> 交流Q群: 893531731
