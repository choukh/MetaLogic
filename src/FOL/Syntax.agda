module FOL.Syntax where

open import Foundation.Essential
open import Foundation.Data.List.SetTheoretic

record Language : 𝕋₁ where
  field
    ℱ : 𝕋
    ℛ : 𝕋
    ∣_∣ᶠ : ℱ → ℕ
    ∣_∣ᴿ : ℛ → ℕ
    discreteℱ : discrete ℱ
    discreteℛ : discrete ℛ
    enumerableℱ : enumerable ℱ
    enumerableℛ : enumerable ℛ

  countableℱ : countable ℱ
  countableℱ = discrete→enumerable→countable discreteℱ enumerableℱ

  countableℛ : countable ℛ
  countableℛ = discrete→enumerable→countable discreteℛ enumerableℛ

open Language ⦃...⦄

module _ ⦃ ℒ : Language ⦄ where

  data Term : 𝕋 where
    #_ : ℕ → Term
    _$̇_ : (f : ℱ) → 𝕍 Term ∣ f ∣ᶠ → Term

  data Formula : 𝕋 where
    ⊥̇ : Formula
    _$̇_ : (R : ℛ) → 𝕍 Term ∣ R ∣ᴿ → Formula
    _→̇_ : Formula → Formula → Formula
    ∀̇_ : Formula → Formula

  Subst : 𝕋
  Subst = ℕ → Term

  infix 30 _[_]ₜ _[_]ₜ⃗
  _[_]ₜ : Term → Subst → Term
  _[_]ₜ⃗ : ∀ {n} → 𝕍 Term n → Subst → 𝕍 Term n

  (# n)   [ σ ]ₜ = σ n
  (f $̇ t⃗) [ σ ]ₜ = f $̇ t⃗ [ σ ]ₜ⃗

  [] [ σ ]ₜ⃗ = []
  (t ∷ t⃗) [ σ ]ₜ⃗ = t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗

  ↑ₜ : Term → Term
  ↑ₜ = _[ #_ ∘ suc ]ₜ

  infix 8 _;_
  _;_ : Term → Subst → Subst
  (t ; σ) zero = t
  (t ; σ) (suc n) = σ n

  infix 30 _[_]ᵩ
  _[_]ᵩ : Formula → Subst → Formula
  ⊥̇       [ σ ]ᵩ = ⊥̇
  (R $̇ t⃗) [ σ ]ᵩ = R $̇ t⃗ [ σ ]ₜ⃗
  (φ →̇ ψ) [ σ ]ᵩ = φ [ σ ]ᵩ →̇ ψ [ σ ]ᵩ
  (∀̇ φ)   [ σ ]ᵩ = ∀̇ φ [ # 0 ; ↑ₜ ∘ σ ]ᵩ

  ↑ᵩ : Formula → Formula
  ↑ᵩ = _[ #_ ∘ suc ]ᵩ

  _[_;] : Formula → Term → Formula
  φ [ t ;] = φ [ t ; #_ ]ᵩ

  Context : 𝕋
  Context = 𝕃 Formula

  ↑ : Context → Context
  ↑ = map ↑ᵩ

  Theory : 𝕋₁
  Theory = 𝒫 Formula

  variable
    t : Term
    φ ψ : Formula
    Γ : Context
    𝒯 : Theory

  infix 10 _⊢_
  data _⊢_ : Context → Formula → 𝕋 where
    Ctx     : φ ∈ Γ             → Γ ⊢ φ
    ImpI    : (φ ∷ Γ) ⊢ ψ       → Γ ⊢ φ →̇ ψ
    ImpE    : Γ ⊢ φ →̇ ψ → Γ ⊢ φ → Γ ⊢ ψ
    AllI    : ↑ Γ ⊢ φ           → Γ ⊢ ∀̇ φ
    AllE    : Γ ⊢ ∀̇ φ           → Γ ⊢ φ [ t ;]
    FalseE  : Γ ⊢ ⊥̇             → Γ ⊢ φ
    Peirce  : Γ ⊢ ((φ →̇ ψ) →̇ φ) →̇ φ
