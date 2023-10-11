module FOL.Syntax where

open import Foundation.Everything

record Language : 𝒰₁ where
  field
    ℱ : 𝒰
    𝒫 : 𝒰
    ∣_∣ₜ : ℱ → ℕ
    ∣_∣ᵩ : 𝒫 → ℕ

open Language ⦃...⦄

module _ ⦃ ℒ : Language ⦄ where

  data Term : 𝒰 where
    #_ : ℕ → Term
    _$̇̇_ : (f : ℱ) → 𝕍 Term ∣ f ∣ₜ → Term

  data Formula : 𝒰 where
    ⊥̇ : Formula
    _$̇̇_ : (P : 𝒫) → 𝕍 Term ∣ P ∣ᵩ → Formula
    _→̇_ : Formula → Formula → Formula
    ∀̇_ : Formula → Formula

  Subst : 𝒰
  Subst = ℕ → Term

  infix 30 _[_]ₜ _[_]ₜ⃗
  _[_]ₜ : Term → Subst → Term
  _[_]ₜ⃗ : ∀ {n} → 𝕍 Term n → Subst → 𝕍 Term n

  (# n)   [ σ ]ₜ = σ n
  (f $̇̇ t⃗) [ σ ]ₜ = f $̇̇ t⃗ [ σ ]ₜ⃗

  [] [ σ ]ₜ⃗ = []
  (t ∷ t⃗) [ σ ]ₜ⃗ = t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗

  infix 8 _;_
  _;_ : Term → Subst → Subst
  (t ; σ) zero = t
  (t ; σ) (suc n) = σ n

  ↑ₜ : Term → Term
  ↑ₜ = _[ #_ ∘ suc ]ₜ

  infix 30 _[_]ᵩ
  _[_]ᵩ : Formula → Subst → Formula
  ⊥̇       [ σ ]ᵩ = ⊥̇
  (P $̇̇ t⃗) [ σ ]ᵩ = P $̇̇ t⃗ [ σ ]ₜ⃗
  (φ →̇ ψ) [ σ ]ᵩ = φ [ σ ]ᵩ →̇ ψ [ σ ]ᵩ
  (∀̇ φ)   [ σ ]ᵩ = ∀̇ φ [ # 0 ; ↑ₜ ∘ σ ]ᵩ

  ↑ᵩ : Formula → Formula
  ↑ᵩ = _[ #_ ∘ suc ]ᵩ

  _[_] : Formula → Term → Formula
  φ [ t ] = φ [ t ; #_ ]ᵩ

  Context : 𝒰
  Context = 𝕃 Formula

  data HasPeirce : 𝒰 where
    classical intuitionistic : HasPeirce

  data HasECQ : 𝒰 where
    standard paraconsistent : HasECQ

  ProofTree : {p : HasPeirce} {e : HasECQ} → Context → Formula → 𝒰
  ProofTree = {!   !}
