open import FOL.Language
module FOL.Semantics (ℒ : Language) where

open import Foundation.Essential
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)

open Language ℒ
open import FOL.Syntax ℒ

record Interpretation (Domain : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  infix 10 _⊨ₜ_ _⊨ₜ⃗_ _⊨ᵩ_ _⊨_ _⊫_

  field
    funMap : (f : 𝓕) → 𝕍 Domain ∣ f ∣ᶠ → Domain
    relMap : (r : 𝓡) → 𝕍 Domain ∣ r ∣ᴿ → ℙ ℓ
    bottom : ℙ ℓ

  Assignment : 𝕋 _
  Assignment = ℕ → Domain

  _⊨ₜ_ : Assignment → Term → Domain
  _⊨ₜ⃗_ : ∀ {n} → Assignment → 𝕍 Term n → 𝕍 Domain n

  𝓋 ⊨ₜ # n = 𝓋 n
  𝓋 ⊨ₜ f $̇ t⃗ = funMap f (𝓋 ⊨ₜ⃗ t⃗)

  𝓋 ⊨ₜ⃗ [] = []
  𝓋 ⊨ₜ⃗ (t ∷ t⃗) = 𝓋 ⊨ₜ t ∷ 𝓋 ⊨ₜ⃗ t⃗

  ⊨ₜ⃗≡map⃗ : ∀ 𝓋 {n} (t⃗ : 𝕍 Term n) → 𝓋 ⊨ₜ⃗ t⃗ ≡ map⃗ (𝓋 ⊨ₜ_) t⃗
  ⊨ₜ⃗≡map⃗ 𝓋 [] = refl
  ⊨ₜ⃗≡map⃗ 𝓋 (x ∷ t⃗) = cong (_ ∷_) $ ⊨ₜ⃗≡map⃗ 𝓋 t⃗

  _⊨ᵩ_ : Assignment → Formula → 𝕋 _
  𝓋 ⊨ᵩ ⊥̇ = bottom holds
  𝓋 ⊨ᵩ R $̇ t⃗ = relMap R (map⃗ (𝓋 ⊨ₜ_) t⃗) holds
  𝓋 ⊨ᵩ φ →̇ ψ = 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ
  𝓋 ⊨ᵩ ∀̇ φ = (x : Domain) → (x ∷ₛ 𝓋) ⊨ᵩ φ

  _⊨_ : Assignment → Context → 𝕋 _
  𝓋 ⊨ Γ = ∀ φ → φ ∈ᴸ Γ → 𝓋 ⊨ᵩ φ

  _⊫_ : Assignment → Theory → 𝕋 _
  𝓋 ⊫ 𝒯 = ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ

open Interpretation ⦃...⦄ public

Variant : ∀ ℓ → 𝕋 _
Variant ℓ = {D : 𝕋 ℓ} → ⦃ Interpretation D ⦄ → 𝕋 ℓ

_⊑_ : Variant ℓ → Variant ℓ → 𝕋 _
C₁ ⊑ C₂ = ∀ {D} ⦃ _ : Interpretation D ⦄ → C₁ → C₂

Classical : Variant ℓ
Classical = ∀ 𝓋 φ ψ → 𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ

StandardBottom : Variant ℓ
StandardBottom = bottom holds → ⊥

ExplodingBottom : Variant ℓ
ExplodingBottom = ∀ 𝓋 R t⃗ → 𝓋 ⊨ᵩ ⊥̇ →̇ R $̇ t⃗

Standard : Variant ℓ
Standard = Classical ∧ StandardBottom

Exploding : Variant ℓ
Exploding = Classical ∧ ExplodingBottom

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
    𝓋 : Assignment

_isA_modelOf_ : Model ℓ → Variant ℓ → Theory → 𝕋 _
ℳ isA C modelOf 𝒯 = C ∧ ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ
  where open Model ℳ
