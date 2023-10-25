module FOL.Syntax where

open import Foundation.Essential
open import Foundation.Data.List.SetTheoretic

record Language : 𝕋₁ where
  field
    𝔣 : 𝕋
    𝔓 : 𝕋
    ∣_∣ₜ : 𝔣 → ℕ
    ∣_∣ᵩ : 𝔓 → ℕ
    discrete𝔣 : discrete 𝔣
    discrete𝔓 : discrete 𝔓
    enumerable𝔣 : enumerable 𝔣
    enumerable𝔓 : enumerable 𝔓

  countable𝔣 : countable 𝔣
  countable𝔣 = discrete→enumerable→countable discrete𝔣 enumerable𝔣

  countable𝔓 : countable 𝔓
  countable𝔓 = discrete→enumerable→countable discrete𝔓 enumerable𝔓

open Language ⦃...⦄

module _ ⦃ ℒ : Language ⦄ where

  data Term : 𝕋 where
    #_ : ℕ → Term
    _$̇_ : (f : 𝔣) → 𝕍 Term ∣ f ∣ₜ → Term

  data Formula : 𝕋 where
    ⊥̇ : Formula
    _$̇_ : (P : 𝔓) → 𝕍 Term ∣ P ∣ᵩ → Formula
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
  (P $̇ t⃗) [ σ ]ᵩ = P $̇ t⃗ [ σ ]ₜ⃗
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
