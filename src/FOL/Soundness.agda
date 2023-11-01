open import FOL.Language
module FOL.Soundness (ℒ : Language) where

open import Foundation.Essential
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)

open import FOL.Syntax ℒ
open import FOL.Semantics ℒ

semanticExplosion : ⦃ _ : Interpretation D ⦄ → ExplodingBottom →
  ∀ 𝓋 φ → 𝓋 ⊨ᵩ ⊥̇ → 𝓋 ⊨ᵩ φ
semanticExplosion exp 𝓋 ⊥̇ bot = bot
semanticExplosion exp 𝓋 (R $̇ t⃗) bot = exp 𝓋 R t⃗ bot
semanticExplosion exp 𝓋 (φ →̇ ψ) bot _ = semanticExplosion exp 𝓋 ψ bot
semanticExplosion exp 𝓋 (∀̇ φ) bot x = semanticExplosion exp (x ∷ₛ 𝓋) φ bot

⊨ₜ-∘ : ⦃ _ : Interpretation D ⦄ →
  ∀ 𝓋 σ t → (𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ t ≡ 𝓋 ⊨ₜ t [ σ ]ₜ
⊨ₜ-∘ 𝓋 σ t = {!   !}

⊨ᵩ-∘ : ⦃ _ : Interpretation D ⦄ →
  ∀ 𝓋 φ σ → (𝓋 ⊨ₜ_ ∘ σ) ⊨ᵩ φ ↔ 𝓋 ⊨ᵩ φ [ σ ]ᵩ
⊨ᵩ-∘ 𝓋 ⊥̇ σ = ↔-refl
⊨ᵩ-∘ 𝓋 (R $̇ t⃗) σ = ↔-cong (λ t → relMap R t holds) H where
  H = map⃗ ((𝓋 ⊨ₜ_ ∘ σ) ⊨ₜ_) t⃗       ≡⟨ cong (λ f → map⃗ f t⃗) (funExt $ ⊨ₜ-∘ 𝓋 σ) ⟩
      map⃗ (𝓋 ⊨ₜ_ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map-∘ (𝓋 ⊨ₜ_) (_[ σ ]ₜ) t⃗ ⟩
      map⃗ (𝓋 ⊨ₜ_) (map⃗ (_[ σ ]ₜ) t⃗) ∎
⊨ᵩ-∘ 𝓋 (φ →̇ ψ) σ = ↔-cong-→ (⊨ᵩ-∘ 𝓋 φ σ) (⊨ᵩ-∘ 𝓋 ψ σ)
⊨ᵩ-∘ 𝓋 (∀̇ φ) σ = {!   !}

soundness⟨_⟩ : (C : Variant ℓ) → C ⊑ Exploding →
  ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨⟨ C ⟩ φ
soundness⟨ C ⟩ H (Ctx φ∈Γ) _ _ 𝓋⊨Γ = 𝓋⊨Γ _ φ∈Γ
soundness⟨ C ⟩ H (ImpI IH) c 𝓋 𝓋⊨Γ 𝓋⊨φ = soundness⟨ C ⟩ H IH c 𝓋
  λ { φ (here refl) → 𝓋⊨φ
    ; φ (there φ∈Γ) → 𝓋⊨Γ φ φ∈Γ }
soundness⟨ C ⟩ H (ImpE IH₁ IH₂) c 𝓋 𝓋⊨Γ = soundness⟨ C ⟩ H IH₁ c 𝓋 𝓋⊨Γ $ soundness⟨ C ⟩ H IH₂ c 𝓋 𝓋⊨Γ
soundness⟨ C ⟩ H (AllI IH) c 𝓋 𝓋⊨Γ x = soundness⟨ C ⟩ H IH c (x ∷ₛ 𝓋) $
  map⊆P-intro λ φ φ∈Γ → {! 𝓋⊨Γ (↑ᵩ φ)  !}
soundness⟨ C ⟩ H (AllE IH) = {!   !}
soundness⟨ C ⟩ H (FalseE {φ} Γ⊢⊥̇) c 𝓋 𝓋⊨Γ = semanticExplosion (H c .snd) 𝓋 φ $ soundness⟨ C ⟩ H Γ⊢⊥̇ c 𝓋 𝓋⊨Γ
soundness⟨ C ⟩ H (Peirce φ ψ) c 𝓋 _ = H c .fst 𝓋 φ ψ

soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨⟨ Standard {ℓ} ⟩ φ
soundness Γ⊢φ = soundness⟨ Standard ⟩ Std⊑Exp Γ⊢φ

instance
  ℐ : Interpretation ⊤
  ℐ = record
    { funMap = λ _ _ → tt
    ; relMap = λ _ _ → ⊥ , isProp⊥
    ; bottom = ⊥ , isProp⊥ }

Dec⊨ᵩ : (𝓋 : Assignment) (φ : Formula) → Dec (𝓋 ⊨ᵩ φ)
Dec⊨ᵩ 𝓋 ⊥̇       = no λ ()
Dec⊨ᵩ 𝓋 (R $̇ x) = no λ ()
Dec⊨ᵩ 𝓋 (φ →̇ ψ) with Dec⊨ᵩ 𝓋 φ | Dec⊨ᵩ 𝓋 ψ
... | yes p | yes q = yes λ _ → q
... | yes p | no ¬q = no λ pq → ¬q $ pq p
... | no ¬p | _     = yes λ p → exfalso $ ¬p p
Dec⊨ᵩ 𝓋 (∀̇ φ) with Dec⊨ᵩ (tt ∷ₛ 𝓋) φ
... | yes p = yes λ { tt → p }
... | no ¬p = no λ p → ¬p $ p tt

classical : Classical
classical 𝓋 φ ψ pierce with Dec⊨ᵩ 𝓋 φ
... | yes p = p
... | no ¬p = exfalso $ ¬p $ pierce λ p → exfalso $ ¬p p

standard : Standard
standard = classical , id

consistency : [] ⊬ ⊥̇
consistency ⊢⊥̇ = soundness ⊢⊥̇ standard (λ _ → tt) λ _ ()
