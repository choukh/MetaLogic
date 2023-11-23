---
url: fol.semantics
---

# 一阶逻辑: 语义

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Semantics (ℒ : Language) where

open Language ℒ
open import FOL.Syntax ℒ

record Interpretation (Domain : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  infix 10 _⊨ₜ_ _⊨ₜ⃗_ _⊨ᵩ_ _⊨_ _⊫_

  field
    fᴵ : (f : 𝓕) → 𝕍 Domain ∣ f ∣ᶠ → Domain
    Rᴵ : (R : 𝓡) → 𝕍 Domain ∣ R ∣ᴿ → ℙ ℓ
    ⊥ᴵ : ℙ ℓ

  Valuation : 𝕋 _
  Valuation = ℕ → Domain

  _⊨ₜ_ : Valuation → Term → Domain
  _⊨ₜ⃗_ : ∀ {n} → Valuation → 𝕍 Term n → 𝕍 Domain n

  𝓋 ⊨ₜ # n = 𝓋 n
  𝓋 ⊨ₜ f $̇ t⃗ = fᴵ f (𝓋 ⊨ₜ⃗ t⃗)

  𝓋 ⊨ₜ⃗ [] = []
  𝓋 ⊨ₜ⃗ (t ∷ t⃗) = 𝓋 ⊨ₜ t ∷ 𝓋 ⊨ₜ⃗ t⃗

  ⊨ₜ⃗≡map⃗ : ∀ 𝓋 {n} (t⃗ : 𝕍 Term n) → 𝓋 ⊨ₜ⃗ t⃗ ≡ map⃗ (𝓋 ⊨ₜ_) t⃗
  ⊨ₜ⃗≡map⃗ 𝓋 [] = refl
  ⊨ₜ⃗≡map⃗ 𝓋 (x ∷ t⃗) = cong (_ ∷_) $ ⊨ₜ⃗≡map⃗ 𝓋 t⃗

  _⊨ᵩ_ : Valuation → Formula → 𝕋 _
  𝓋 ⊨ᵩ ⊥̇ = ⊥ᴵ holds
  𝓋 ⊨ᵩ φ →̇ ψ = 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ
  𝓋 ⊨ᵩ ∀̇ φ = (x : Domain) → (x ∷ₙ 𝓋) ⊨ᵩ φ
  𝓋 ⊨ᵩ R $̇ t⃗ = Rᴵ R (map⃗ (𝓋 ⊨ₜ_) t⃗) holds

  _⊨_ : Valuation → Context → 𝕋 _
  𝓋 ⊨ Γ = ∀ φ → φ ∈ᴸ Γ → 𝓋 ⊨ᵩ φ

  _⊫_ : Valuation → Theory → 𝕋 _
  𝓋 ⊫ 𝒯 = ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ

open Interpretation ⦃...⦄ public

Variant : ∀ ℓ → 𝕋 _
Variant ℓ = {D : 𝕋 ℓ} → ⦃ Interpretation D ⦄ → 𝕋 ℓ

_⊑_ : Variant ℓ → Variant ℓ → 𝕋 _
C₁ ⊑ C₂ = ∀ {D} ⦃ _ : Interpretation D ⦄ → C₁ → C₂

Classical : Variant ℓ
Classical = ∀ 𝓋 φ ψ → 𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ

Standard⊥ᴵ : Variant ℓ
Standard⊥ᴵ = ⊥ᴵ holds → ⊥

Exploding⊥ᴵ : Variant ℓ
Exploding⊥ᴵ = ∀ 𝓋 R t⃗ → 𝓋 ⊨ᵩ ⊥̇ →̇ R $̇ t⃗

Standard : Variant ℓ
Standard = Classical ∧ Standard⊥ᴵ

Exploding : Variant ℓ
Exploding = Classical ∧ Exploding⊥ᴵ

Std⊑Exp : Standard {ℓ} ⊑ Exploding
Std⊑Exp (cls , std⊥) = cls , λ _ _ _ → exfalso ∘ std⊥

_⊨⟨_⟩_ : Context → Variant ℓ → Formula → 𝕋 _
Γ ⊨⟨ C ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → C → ∀ 𝓋 → 𝓋 ⊨ Γ → 𝓋 ⊨ᵩ φ

_⊫⟨_⟩_ : Theory → Variant ℓ → Formula → 𝕋 _
𝒯 ⊫⟨ C ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → C → ∀ 𝓋 → 𝓋 ⊫ 𝒯 → 𝓋 ⊨ᵩ φ

record Model ℓ : 𝕋 (ℓ ⁺) where
  field
    Domain : 𝕋 ℓ
    ⦃ ℐ ⦄ : Interpretation Domain
    𝓋 : Valuation

_isA_modelOf_ : Model ℓ → Variant ℓ → Theory → 𝕋 _
ℳ isA C modelOf 𝒯 = C ∧ ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ
  where open Model ℳ
```
