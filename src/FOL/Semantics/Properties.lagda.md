---
url: fol.semantics.properties
---

# 一阶逻辑 ▸ 语义 ▸ 性质

```agda
open import FOL.Language
module FOL.Semantics.Properties (ℒ : Language) where

open import Foundation.Essential
open import Foundation.Data.Vec.SetTheoretic
  renaming (_∈_ to _∈⃗_)

open import FOL.Syntax ℒ
open import FOL.Syntax.Properties ℒ
open import FOL.Semantics ℒ

⊨ₜ-∘ : ⦃ _ : Interpretation D ⦄ →
  ∀ 𝓋 σ t → (𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ t ≡ 𝓋 ⊨ₜ t [ σ ]ₜ
⊨ₜ-∘ 𝓋 σ = term-elim (λ _ → refl) H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → (_⊨ₜ_ 𝓋 ∘ σ) ⊨ₜ t ≡ 𝓋 ⊨ₜ t [ σ ]ₜ) →
    (𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ f $̇ t⃗ ≡ 𝓋 ⊨ₜ (f $̇ t⃗) [ σ ]ₜ
  H f t⃗ IH = cong (fᴵ f) H2 where
    H2 : (𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ⃗ t⃗ ≡ 𝓋 ⊨ₜ⃗ t⃗ [ σ ]ₜ⃗
    H2 rewrite ⊨ₜ⃗≡map⃗ (𝓋 ⊨ₜ_ ∘ σ) t⃗ | ⊨ₜ⃗≡map⃗ 𝓋 (t⃗ [ σ ]ₜ⃗) | []ₜ⃗≡map⃗ t⃗ σ =
      map⃗ ((𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ_) t⃗       ≡⟨ map-ext IH ⟩
      map⃗ (𝓋 ⊨ₜ_ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map-∘ _ _ _ ⟩
      map⃗ (𝓋 ⊨ₜ_) (map⃗ (_[ σ ]ₜ) t⃗) ∎

∷ₙ⊨ₜ↑ₜ : ⦃ _ : Interpretation D ⦄ →
  ∀ (x : D) 𝓋 t → 𝓋 ⊨ₜ t ≡ (x ∷ₙ 𝓋) ⊨ₜ ↑ₜ t
∷ₙ⊨ₜ↑ₜ x 𝓋 t = ⊨ₜ-∘ (x ∷ₙ 𝓋) (#_ ∘ suc) t

⊨ₜ-ext : ⦃ _ : Interpretation D ⦄ →
  ∀ {𝓋 𝓊} → 𝓋 ≗ 𝓊 → ∀ t → 𝓋 ⊨ₜ t ≡ 𝓊 ⊨ₜ t
⊨ₜ-ext {𝓋} {𝓊} eq = term-elim eq H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → 𝓋 ⊨ₜ t ≡ 𝓊 ⊨ₜ t) → 𝓋 ⊨ₜ (f $̇ t⃗) ≡ 𝓊 ⊨ₜ (f $̇ t⃗)
  H f t⃗ IH rewrite ⊨ₜ⃗≡map⃗ 𝓋 t⃗ | ⊨ₜ⃗≡map⃗ 𝓊 t⃗ = cong (fᴵ f) (map-ext IH)

⊨ᵩ-ext : ⦃ _ : Interpretation D ⦄ →
  ∀ {𝓋 𝓊} → 𝓋 ≗ 𝓊 → ∀ φ → 𝓋 ⊨ᵩ φ ↔ 𝓊 ⊨ᵩ φ
⊨ᵩ-ext eq ⊥̇ = ↔-refl
⊨ᵩ-ext eq (R $̇ t⃗) = ↔-cong (λ t → Rᴵ R t holds) (map-cong (⊨ₜ-ext eq) t⃗)
⊨ᵩ-ext eq (φ →̇ ψ) = ↔-cong-→ (⊨ᵩ-ext eq φ) (⊨ᵩ-ext eq ψ)
⊨ᵩ-ext {𝓋} {𝓊} eq (∀̇ φ) = ↔-cong-Π λ x → ⊨ᵩ-ext (H x) φ where
  H : ∀ x → x ∷ₙ 𝓋 ≗ x ∷ₙ 𝓊
  H x zero = refl
  H x (suc n) = eq n

⊨ᵩ-∘ : ⦃ _ : Interpretation D ⦄ →
  ∀ 𝓋 φ σ → (𝓋 ⊨ₜ_ ∘ σ) ⊨ᵩ φ ↔ 𝓋 ⊨ᵩ φ [ σ ]ᵩ
⊨ᵩ-∘ 𝓋 ⊥̇ σ = ↔-refl
⊨ᵩ-∘ 𝓋 (R $̇ t⃗) σ = ↔-cong (λ t → Rᴵ R t holds) H where
  H = map⃗ ((𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ_) t⃗       ≡⟨ map-cong (⊨ₜ-∘ 𝓋 σ) t⃗ ⟩
      map⃗ (𝓋 ⊨ₜ_ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map-∘ _ _ _ ⟩
      map⃗ (𝓋 ⊨ₜ_) (map⃗ (_[ σ ]ₜ) t⃗) ∎
⊨ᵩ-∘ 𝓋 (φ →̇ ψ) σ = ↔-cong-→ (⊨ᵩ-∘ 𝓋 φ σ) (⊨ᵩ-∘ 𝓋 ψ σ)
⊨ᵩ-∘ 𝓋 (∀̇ φ) σ = ↔-cong-Π λ x →
  (x ∷ₙ (𝓋 ⊨ₜ_) ∘ σ) ⊨ᵩ φ               ↔⟨ ⊨ᵩ-ext (H x) φ ⟩
  ((x ∷ₙ 𝓋) ⊨ₜ_ ∘ (# 0 ∷ₙ ↑ₜ ∘ σ)) ⊨ᵩ φ ↔⟨ ⊨ᵩ-∘ (x ∷ₙ 𝓋) φ (# 0 ∷ₙ ↑ₜ ∘ σ) ⟩
  (x ∷ₙ 𝓋) ⊨ᵩ φ [ # 0 ∷ₙ ↑ₜ ∘ σ ]ᵩ      ↔∎
  where
  H : ∀ x → x ∷ₙ (𝓋 ⊨ₜ_) ∘ σ ≗ (x ∷ₙ 𝓋) ⊨ₜ_ ∘ (# 0 ∷ₙ ↑ₜ ∘ σ)
  H x zero = refl
  H x (suc n) = ∷ₙ⊨ₜ↑ₜ x 𝓋 (σ n)

∷ₙ⊨ᵩ↑ᵩ : ⦃ _ : Interpretation D ⦄ →
  ∀ (x : D) 𝓋 φ → 𝓋 ⊨ᵩ φ ↔ (x ∷ₙ 𝓋) ⊨ᵩ ↑ᵩ φ
∷ₙ⊨ᵩ↑ᵩ x 𝓋 φ = ⊨ᵩ-∘ (x ∷ₙ 𝓋) φ (#_ ∘ suc)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Semantics/Properties.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Semantics.Properties.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.semantics.properties)  
> 交流Q群: 893531731
