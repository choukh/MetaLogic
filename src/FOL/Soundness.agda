open import FOL.Language
module FOL.Soundness (ℒ : Language) where

open import Foundation.Essential
open import FOL.Syntax ℒ
open import FOL.Semantics ℒ

soundness⟨_⟩ : (C : Variant ℓ) → C ⊑ Exploding → ∀ Γ φ → Γ ⊢ φ → Γ ⊨⟨ C ⟩ φ
soundness⟨ C ⟩ exp Γ φ (Ctx x) c 𝓋 𝓋⊨Γ = {!   !}
soundness⟨ C ⟩ exp Γ (φ →̇ ψ) (ImpI ⊢) = {!   !}
soundness⟨ C ⟩ exp Γ φ (ImpE ⊢₁ ⊢₂) = {!   !}
soundness⟨ C ⟩ exp Γ (∀̇ φ) (AllI ⊢) = {!   !}
soundness⟨ C ⟩ exp Γ _ (AllE ⊢) = {!   !}
soundness⟨ C ⟩ exp Γ φ (FalseE ⊢) = {!   !}
soundness⟨ C ⟩ exp Γ _ Peirce = {!   !}

soundness : ∀ Γ φ → Γ ⊢ φ → Γ ⊨⟨ Standard {ℓ} ⟩ φ
soundness Γ φ Γ⊢φ = soundness⟨ Standard ⟩ Std⊑Exp Γ φ Γ⊢φ

instance
  ℐ : Interpretation ⊤
  ℐ = record
    { funMap = λ _ _ → tt
    ; relMap = λ _ _ → ⊥ , isProp⊥
    ; bottom = ⊥ , isProp⊥ }

Dec⊨ᵩ : (𝓋 : Assignment) (φ : Formula) → Dec (𝓋 ⊨ᵩ φ)
Dec⊨ᵩ 𝓋 ⊥̇       = no (λ ())
Dec⊨ᵩ 𝓋 (R $̇ x) = no (λ ())
Dec⊨ᵩ 𝓋 (φ →̇ ψ) with Dec⊨ᵩ 𝓋 φ | Dec⊨ᵩ 𝓋 ψ
... | yes p | yes q = yes λ _ → q
... | yes p | no ¬q = no λ pq → ¬q $ pq p
... | no ¬p | _     = yes λ p → exfalso $ ¬p p
Dec⊨ᵩ 𝓋 (∀̇ φ) with Dec⊨ᵩ (tt ; 𝓋) φ
... | yes p = yes λ { tt → p }
... | no ¬p = no λ p → ¬p $ p tt

classical : Classical
classical 𝓋 φ ψ pierce with Dec⊨ᵩ 𝓋 φ
... | yes p = p
... | no ¬p = exfalso $ ¬p $ pierce λ p → exfalso $ ¬p p

standard : Standard
standard = classical , id

consistency : [] ⊬ ⊥̇
consistency ⊢⊥̇ = soundness [] ⊥̇ ⊢⊥̇ standard (λ _ → tt) λ _ ()
