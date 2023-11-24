---
url: fol.soundness
---

# 一阶逻辑: 可靠性

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Soundness (ℒ : Language) where

open import FOL.Syntax ℒ
open import FOL.Syntax.Properties ℒ
open import FOL.Semantics ℒ
open import FOL.Semantics.Properties ℒ

semanticExplosion : ⦃ _ : Interpretation D ⦄ → Exploding⊥ →
  ∀ 𝓋 φ → 𝓋 ⊨ᵩ ⊥̇ → 𝓋 ⊨ᵩ φ
semanticExplosion exp 𝓋 ⊥̇ bot = bot
semanticExplosion exp 𝓋 (R $̇ t⃗) bot = exp 𝓋 R t⃗ bot
semanticExplosion exp 𝓋 (φ →̇ ψ) bot _ = semanticExplosion exp 𝓋 ψ bot
semanticExplosion exp 𝓋 (∀̇ φ) bot x = semanticExplosion exp (x ∷ₙ 𝓋) φ bot

soundness⟨_⟩ : (C : Variant ℓ) → Exp ⊑ C →
  ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨⟨ C ⟩ φ
soundness⟨ C ⟩ _ (Ctx φ∈Γ) _ _ 𝓋⊨Γ = 𝓋⊨Γ _ φ∈Γ
soundness⟨ C ⟩ Γ⊢ (ImpI H) c 𝓋 𝓋⊨Γ 𝓋⊨φ = soundness⟨ C ⟩ Γ⊢ H c 𝓋
  λ { φ (here refl) → 𝓋⊨φ
    ; φ (there φ∈Γ) → 𝓋⊨Γ φ φ∈Γ }
soundness⟨ C ⟩ Γ⊢ (ImpE H₁ H₂) c 𝓋 𝓋⊨Γ = soundness⟨ C ⟩ Γ⊢ H₁ c 𝓋 𝓋⊨Γ $ soundness⟨ C ⟩ Γ⊢ H₂ c 𝓋 𝓋⊨Γ
soundness⟨ C ⟩ Γ⊢ (AllI H) c 𝓋 𝓋⊨Γ x = soundness⟨ C ⟩ Γ⊢ H c (x ∷ₙ 𝓋) $
  map⊆P-intro λ φ φ∈Γ → ∷ₙ⊨ᵩ↑ᵩ x 𝓋 φ .⇒ $ 𝓋⊨Γ φ φ∈Γ

soundness⟨ C ⟩ Γ⊢ (AllE {φ} {t} H) c 𝓋 𝓋⊨Γ = H1 where
  H1 : 𝓋 ⊨ᵩ φ [ t ∷]
  H1 = ⊨ᵩ-∘ 𝓋 φ (t ∷ₙ #_) .⇒ H2 where
    H2 : (𝓋 ⊨ₜ_ ∘ (t ∷ₙ #_)) ⊨ᵩ φ
    H2 = ⊨ᵩ-ext eq φ .⇒ H3 where
      H3 : ((𝓋 ⊨ₜ t) ∷ₙ 𝓋) ⊨ᵩ φ
      H3 = soundness⟨ C ⟩ Γ⊢ H c 𝓋 𝓋⊨Γ (𝓋 ⊨ₜ t)
      eq : ∀ n → ((𝓋 ⊨ₜ t) ∷ₙ 𝓋) n ≡ 𝓋 ⊨ₜ (t ∷ₙ #_) n
      eq zero = refl
      eq (suc n) = refl

soundness⟨ C ⟩ Γ⊢ (FalseE {φ} Γ⊢⊥̇) c 𝓋 𝓋⊨Γ = semanticExplosion (Γ⊢ c .snd) 𝓋 φ $ soundness⟨ C ⟩ Γ⊢ Γ⊢⊥̇ c 𝓋 𝓋⊨Γ
soundness⟨ C ⟩ Γ⊢ (Peirce φ ψ) c 𝓋 _ = Γ⊢ c .fst 𝓋 φ ψ

soundness : Γ ⊢ φ → Γ ⊨ φ
soundness Γ⊢φ = soundness⟨ Std ⟩ Exp⊑Std Γ⊢φ

instance
  ℐ : Interpretation ⊤
  ℐ = record
    { fᴵ = λ _ _ → tt
    ; Rᴵ = λ _ _ → ⊥ₚ
    ; ⊥ᴵ = ⊥ₚ }

Dec⊨ᵩ : (𝓋 : Valuation ⊤) (φ : Formula) → Dec (𝓋 ⊨ᵩ φ)
Dec⊨ᵩ 𝓋 ⊥̇       = no λ ()
Dec⊨ᵩ 𝓋 (R $̇ x) = no λ ()
Dec⊨ᵩ 𝓋 (φ →̇ ψ) with Dec⊨ᵩ 𝓋 φ | Dec⊨ᵩ 𝓋 ψ
... | yes p | yes q = yes λ _ → q
... | yes p | no ¬q = no λ pq → ¬q $ pq p
... | no ¬p | _     = yes λ p → exfalso $ ¬p p
Dec⊨ᵩ 𝓋 (∀̇ φ) with Dec⊨ᵩ (tt ∷ₙ 𝓋) φ
... | yes p = yes λ { tt → p }
... | no ¬p = no λ p → ¬p $ p tt

classical : Classical
classical 𝓋 φ ψ pierce with Dec⊨ᵩ 𝓋 φ
... | yes p = p
... | no ¬p = exfalso $ ¬p $ pierce λ p → exfalso $ ¬p p

consistency : [] ⊬ ⊥̇
consistency ⊢⊥̇ = soundness ⊢⊥̇ (classical , id) (λ _ → tt) λ _ ()
```
