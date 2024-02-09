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
  open CompleteExtension (mkComExt 𝒯ᶜ)
    using (𝒯ᵒ; 𝒯ᵒ-sub; 𝒯ᵒ-con; 𝒯ᵒ-C⊢; 𝒯ᵒ-D→̇; 𝒯ᵒ-D∀̇)
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
  std⊥  : Con 𝒯ⁱ → Standard⊥
  std⊥ con ⊥̇∈𝒯ᵒ = 𝟙.rec isProp⊥ con $ 𝒯ᵒ-con ∣ Ctxᵀ ⊥̇∈𝒯ᵒ ∣₁
```

```agda
  modelhood : Con 𝒯ⁱ → ℳ isA Std {Domain = Term} modelOf 𝒯ⁱ
  modelhood con = (cls , std⊥ con) , λ φ φ∈𝒯ⁱ → valid φ (𝒯ᵒ-sub φ∈𝒯ⁱ)
```

## 标准完备性

```agda
module Standard {ℓ} {𝒯 : Theory} {φ : Formula} (c𝒯 : closedᵀ 𝒯) (cφ : closed φ) where
  open PolymorphicSemantics ℓ

  import FOL.Soundness ℒ as S
  open S.Standard using (soundnessᵀ)

  open import FOL.Syntax.Discrete ℒ
  open SetOperation (discreteSet {A = Formula})

  SemiCompleteness    = 𝒯 ⊨ᵀ φ → nonEmpty (𝒯 ⊢ᵀ φ)
  Completeness        = 𝒯 ⊨ᵀ φ → 𝒯 ⊢ᵀ φ
  SyntacticStability  = stable (𝒯 ⊢ᵀ φ)
```

```agda
  semiCompleteness : SemiCompleteness
  semiCompleteness 𝒯⊨φ 𝒯⊬φ = std⊥ con (H₁ H₂) where
    c⨭ : closedᵀ (𝒯 ⨭ ¬̇ φ)
    c⨭ = 𝟙.rec isPropClosed
      λ { (inj₁ ∈𝒯) → c𝒯 ∈𝒯
        ; (inj₂ refl) le → fresh→̇ (cφ le) fresh⊥̇ }
    open TermModel (𝒯 ⨭ ¬̇ φ , c⨭)
    con : Con (𝒯 ⨭ ¬̇ φ)
    con = 𝒯⊬φ ∘ Contraᵀ
    H₁ : # ⊨ᵩ ¬̇ φ
    H₁ = modelhood con .snd (¬̇ φ) (inr refl)
    H₂ : # ⊨ᵩ φ
    H₂ = {!   !}
```

```agda
  completeness↔stability : Completeness ↔ SyntacticStability
  completeness↔stability .⇒ com ne = com $ semanticStability Std id
    λ 𝒯⊭φ → ne λ 𝒯⊢φ → 𝒯⊭φ $ soundnessᵀ 𝒯⊢φ
  completeness↔stability .⇐ stb = stb ∘ semiCompleteness
```

## 爆炸完备性

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Completeness.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Completeness.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.completeness)  
> 交流Q群: 893531731
