open import FOL.Language

module FOL.Semantics (ℒ : Language) where

open import Foundation.Essential
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)

open Language ℒ
open import FOL.Syntax ℒ

record Interpretation (Domain : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  infix 10 _⊨ᵩ_ _⊨_ _⊫_

  field
    funMap : (f : 𝓕) → 𝕍 Domain ∣ f ∣ᶠ → Domain
    relMap : (r : 𝓡) → 𝕍 Domain ∣ r ∣ᴿ → ℙ ℓ
    bottom : ℙ ℓ

  Assignment : 𝕋 _
  Assignment = ℕ → Domain

  eval : Assignment → Term → Domain
  eval⃗ : ∀ {n} → Assignment → 𝕍 Term n → 𝕍 Domain n

  eval 𝓋 (# n) = 𝓋 n
  eval 𝓋 (f $̇ t⃗) = funMap f (eval⃗ 𝓋 t⃗)

  eval⃗ 𝓋 [] = []
  eval⃗ 𝓋 (t ∷ t⃗) = eval 𝓋 t ∷ eval⃗ 𝓋 t⃗

  _⊨ᵩ_ : Assignment → Formula → 𝕋 _
  𝓋 ⊨ᵩ ⊥̇ = bottom holds
  𝓋 ⊨ᵩ R $̇ t⃗ = relMap R (eval⃗ 𝓋 t⃗) holds
  𝓋 ⊨ᵩ φ →̇ ψ = 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ
  𝓋 ⊨ᵩ ∀̇ φ = (x : Domain) → (x ; 𝓋) ⊨ᵩ φ

  _⊨_ : Assignment → Context → 𝕋 _
  𝓋 ⊨ Γ = ∀ φ → φ ∈ᴸ Γ → 𝓋 ⊨ᵩ φ

  _⊫_ : Assignment → Theory → 𝕋 _
  𝓋 ⊫ 𝒯 = ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ

open Interpretation ⦃...⦄

Constraint : ∀ ℓ → 𝕋 _
Constraint ℓ = {D : 𝕋 ℓ} → ⦃ Interpretation D ⦄ → 𝕋 ℓ

classical : Constraint ℓ
classical = ∀ 𝓋 φ ψ → 𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ

standard : Constraint ℓ
standard = classical ∧ (bottom holds → ⊥)

exploding : Constraint ℓ
exploding = classical ∧ ∀ 𝓋 R t⃗ → 𝓋 ⊨ᵩ ⊥̇ →̇ R $̇ t⃗

_⊨⟨_⟩_ : Context → Constraint ℓ → Formula → 𝕋 _
Γ ⊨⟨ C ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → C → ∀ 𝓋 → 𝓋 ⊨ Γ → 𝓋 ⊨ᵩ φ

_⊫⟨_⟩_ : Theory → Constraint ℓ → Formula → 𝕋 _
𝒯 ⊫⟨ C ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → C → ∀ 𝓋 → 𝓋 ⊫ 𝒯 → 𝓋 ⊨ᵩ φ

Model : ∀ ℓ → 𝕋 _
Model ℓ = TypeWithStr ℓ Interpretation

_isA_modelOf_ : Model ℓ → Constraint ℓ → Theory → 𝕋 _
(_ , ℐ) isA C modelOf 𝒯 = let instance _ = ℐ in
  C ∧ ∃ _ λ 𝓋 → ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ

_hasA_model : Theory → Constraint ℓ → 𝕋 _
𝒯 hasA C model = ∃ _ (_isA C modelOf 𝒯)
