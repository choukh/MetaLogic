---
url: fol.completeness
---

# 一阶逻辑 ▸ 完备性

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import FOL.Language
module FOL.Completeness (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
open import FOL.Syntax.SubstitutionFacts ℒ
open import FOL.Syntax.AdmissibleRules ℒ
open import FOL.Syntax.TheoryRules ℒ
open import FOL.Semantics.Base ℒ
open import FOL.TheoryExtension ℒ
```

## 项模型

```agda
module TermModel (𝒯ᶜ@(𝒯ⁱ , _) : ClosedTheory) where
  open CompleteExtension (mkComExt 𝒯ᶜ) using (𝒯ᵒ; 𝒯ᵒ-con; 𝒯ᵒ-C⊢; 𝒯ᵒ-D→̇; 𝒯ᵒ-D∀̇)
```

```agda
  instance
    ℐ : Interpretation Term
    ℐ = record
      { fᴵ = _$̇_
      ; Rᴵ = λ R t⃗ → R $̇ t⃗ ∈ₚ 𝒯ᵒ
      ; ⊥ᴵ = ⊥̇ ∈ₚ 𝒯ᵒ
      }
```

```agda
  ℳ : Structure _
  ℳ = record { ℐ = ℐ ; 𝓋 = # }
```

```agda
  𝓋≡σ : ∀ 𝓋 t → 𝓋 ⊨ₜ t ≡ t [ 𝓋 ]ₜ
  𝓋≡σ 𝓋 = term-elim (λ _ → refl) H$̇ where
    H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → 𝓋 ⊨ₜ t ≡ t [ 𝓋 ]ₜ) → 𝓋 ⊨ₜ f $̇ t⃗ ≡ (f $̇ t⃗) [ 𝓋 ]ₜ
    H$̇ f t⃗ IH rewrite ⊨ₜ⃗≡map⃗ 𝓋 t⃗ | []ₜ⃗≡map⃗ t⃗ 𝓋 = cong (f $̇_) (map⃗-ext IH)
```

```agda
  𝓋↔σ : ∀ 𝓋 φ → 𝓋 ⊨ᵩ φ ↔ φ [ 𝓋 ]ᵩ ∈ 𝒯ᵒ
  𝓋↔σ 𝓋 ⊥̇ = ↔-refl
  𝓋↔σ 𝓋 (φ →̇ ψ) =
    (𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ)               ↔⟨ ↔-cong-→ (𝓋↔σ 𝓋 φ) (𝓋↔σ 𝓋 ψ) ⟩
    (φ [ 𝓋 ]ᵩ ∈ 𝒯ᵒ → ψ [ 𝓋 ]ᵩ ∈ 𝒯ᵒ) ↔˘⟨ 𝒯ᵒ-D→̇ ⟩
    φ [ 𝓋 ]ᵩ →̇ ψ [ 𝓋 ]ᵩ ∈ 𝒯ᵒ        ↔∎
  𝓋↔σ 𝓋 (∀̇ φ) =
    (∀ t → (t ∷ₙ 𝓋) ⊨ᵩ φ)           ↔⟨ ↔-cong-Π iff ⟩
    (∀ t → φ [ ↑ₛ 𝓋 ]ᵩ [ t ]₀ ∈ 𝒯ᵒ) ↔˘⟨ 𝒯ᵒ-D∀̇ ⟩
    ∀̇ φ [ ↑ₛ 𝓋 ]ᵩ ∈ 𝒯ᵒ              ↔∎ where
      iff = λ t →
        (t ∷ₙ 𝓋) ⊨ᵩ φ                   ↔⟨ 𝓋↔σ (t ∷ₙ 𝓋) φ ⟩
        φ [ t ∷ₙ 𝓋 ]ᵩ ∈ 𝒯ᵒ              ↔≡˘⟨ cong (_∈ 𝒯ᵒ) ([]₀∘[↑]ᵩ φ) ⟩
        φ [ ↑ₛ 𝓋 ]ᵩ [ t ]₀ ∈ 𝒯ᵒ         ↔∎
  𝓋↔σ 𝓋 (R $̇ t⃗) = ↔-cong (λ x → R $̇ x ∈ 𝒯ᵒ) (map⃗-ext λ t _ → 𝓋≡σ 𝓋 t)
```

```agda
  ∈→⊨ : ∀ {𝓋} {φ} → φ [ 𝓋 ]ᵩ ∈ 𝒯ᵒ → 𝓋 ⊨ᵩ φ
  ∈→⊨ = 𝓋↔σ _ _ .⇐
```

```agda
  valid : # ⊨ₛᵀ 𝒯ᵒ
  valid φ φ∈𝒯ᵒ = ∈→⊨ $ subst (_∈ 𝒯ᵒ) [#]ᵩ φ∈𝒯ᵒ
```

```agda
  cls : Classical
  cls 𝓋 φ ψ = ∈→⊨ $ 𝒯ᵒ-C⊢ $ tauto $ Peirce _ _
```

```agda
  exp : Exp
  exp = cls , λ 𝓋 R t⃗ → ∈→⊨ $ 𝒯ᵒ-C⊢ $ tauto $ Vac0 Ctx0
```

```agda
  std : Con 𝒯ⁱ → Std
  std con = cls , λ ⊥̇∈𝒯ᵒ → 𝟙.rec isProp⊥ con $ 𝒯ᵒ-con ∣ Ctxᵀ ⊥̇∈𝒯ᵒ ∣₁
```

## 标准完备性

```agda
module Standard {ℓ} where
  open PolymorphicSemantics ℓ

  SemiCompleteness  = ∀ {Γ} {φ} → Γ ⊨ φ → nonEmpty (Γ ⊢ φ)
  SemiCompletenessᵀ = ∀ {𝒯} {φ} → 𝒯 ⊨ᵀ φ → nonEmpty (𝒯 ⊢ᵀ φ)
  Completeness      = ∀ {Γ} {φ} → Γ ⊨ φ → Γ ⊢ φ
  Completenessᵀ     = ∀ {𝒯} {φ} → 𝒯 ⊨ᵀ φ → 𝒯 ⊢ᵀ φ
  Stable⊢           = ∀ {Γ} {φ} → stable (Γ ⊢ φ)
  Stable⊢ᵀ          = ∀ {𝒯} {φ} → stable (𝒯 ⊢ᵀ φ)
```

```agda
  semiCompletenessᵀ : SemiCompletenessᵀ
  semiCompletenessᵀ = {!   !}
```

```agda
  completeness↔stability : Completenessᵀ ↔ Stable⊢ᵀ
  completeness↔stability .⇒ = {!  !}
  completeness↔stability .⇐ = {!   !}
```

## 爆炸完备性

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Completeness.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Completeness.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.completeness)  
> 交流Q群: 893531731
