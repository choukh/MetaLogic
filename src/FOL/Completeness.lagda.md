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
open import FOL.Soundness ℒ
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
  ℳ : Structure ℓ0
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
  valid : # ⊫ₛ 𝒯ᵒ
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

## 完备性

```agda
module _ {𝒯 : Theory} {φ : Formula} (c𝒯 : closedᵀ 𝒯) (cφ : closed φ) where
  open PolymorphicSemantics ℓ0
  open import FOL.Syntax.Discrete ℒ
  open SetOperation (discreteSet {A = Formula})
```

### 标准模型

```agda
  WeakCompleteness    = 𝒯 ⊫ φ → nonEmpty (𝒯 ⊩ φ)
  Completeness        = 𝒯 ⊫ φ → 𝒯 ⊩ φ
  SyntacticStability  = stable (𝒯 ⊩ φ)
```

弱完备性离标准完备性正好就差一个语法稳定性.

```agda
  completeness↔stability : WeakCompleteness → Completeness ↔ SyntacticStability
  completeness↔stability _ .⇒ com ne = com $ semanticStability Std id
    λ 𝒯⊭φ → ne λ 𝒯⊢φ → 𝒯⊭φ $ soundness 𝒯⊢φ
  completeness↔stability wcom .⇐ stb = stb ∘ wcom
```

```agda
  weakCompleteness : WeakCompleteness
  weakCompleteness 𝒯⊨φ 𝒯⊬φ = std⊥ con (H₁ H₂) where
    c⨭ : closedᵀ (𝒯 ⨭ ¬̇ φ)
    c⨭ = 𝟙.rec isPropClosed
      λ { (inj₁ ∈𝒯) → c𝒯 ∈𝒯
        ; (inj₂ refl) le → fresh→̇ (cφ le) fresh⊥̇ }
    open TermModel (𝒯 ⨭ ¬̇ φ , c⨭)
    con : Con (𝒯 ⨭ ¬̇ φ)
    con = 𝒯⊬φ ∘ Contraᵀ
    std = modelhood con .fst
    validate = modelhood con .snd
    H₁ : # ⊨ᵩ ¬̇ φ
    H₁ = validate (¬̇ φ) (inr refl)
    H₂ : # ⊨ᵩ φ
    H₂ = 𝒯⊨φ std # λ φ φ∈𝒯 → validate φ (inl φ∈𝒯)
```

### 爆炸模型

```agda
  ExplodingCompleteness = 𝒯 ⊫⟨ Exp {ℓ0} ⟩ φ → 𝒯 ⊩ φ
  SemanticExplosibility = 𝒯 ⊫ φ → 𝒯 ⊫⟨ Exp {ℓ0} ⟩ φ
```

爆炸完备性离标准完备性正好就差一个语义爆炸性.

```agda
  explosibility↔completeness : ExplodingCompleteness → Completeness ↔ SemanticExplosibility
  explosibility↔completeness ecom .⇒ com 𝒯⊫φ = soundness⟨ Exp ⟩ id (com 𝒯⊫φ)
  explosibility↔completeness ecom .⇐ se 𝒯⊫φ = ecom $ se 𝒯⊫φ
```

```agda
  explodingCompleteness : ExplodingCompleteness
  explodingCompleteness = {!   !}
```

语义爆炸性与语法稳定性等价.

```agda
  explosibility↔stability : SemanticExplosibility ↔ SyntacticStability
  explosibility↔stability =
    SemanticExplosibility ↔˘⟨ explosibility↔completeness explodingCompleteness ⟩
    Completeness          ↔⟨ completeness↔stability weakCompleteness ⟩
    SyntacticStability    ↔∎
```

### 弱构造元理论

TODO

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Completeness.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Completeness.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.completeness)  
> 交流Q群: 893531731
