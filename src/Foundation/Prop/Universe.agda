module Foundation.Prop.Universe where

open import Foundation.Prelude
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation

open import Foundation.Data.Empty
open import Foundation.Data.Unit
open import Foundation.Data.Sigma

open import Cubical.Foundations.HLevels public
  using ()
  renaming (hProp to ℙ🧊)

open import Cubical.Foundations.HLevels
  using (isSetHProp)

import Cubical.Foundations.Univalence as 🧊

--------------------------------------------------------------------------------
-- hProp

ℙ : ∀ ℓ → 𝕋 (ℓ ⁺)
ℙ ℓ = TypeWithStr ℓ isProp

ℙ₀ : 𝕋 (ℓ0 ⁺)
ℙ₀ = ℙ ℓ0

_holds : ℙ ℓ → 𝕋 ℓ
_holds = typ

isPredHolds : isPred (_holds {ℓ})
isPredHolds = str

variable
  𝗣 𝗤 𝗥 : ℙ ℓ

--------------------------------------------------------------------------------
-- Instance

⊥ₚ : ℙ₀
⊥ₚ = ⊥ , isProp⊥

⊤ₚ : ℙ₀
⊤ₚ = ⊤ , isProp⊤

--------------------------------------------------------------------------------
-- Cubical

ℙ→🧊 : ℙ ℓ → ℙ🧊 ℓ
ℙ→🧊 (P , pP) = P , (isProp→🧊 pP)

ℙ←🧊 : ℙ🧊 ℓ → ℙ ℓ
ℙ←🧊 (P , pP) = P , (isProp←🧊 pP)

ℙ→←🧊 : (𝗣 : ℙ🧊 ℓ) → ℙ→🧊 (ℙ←🧊 𝗣) ≡ 𝗣
ℙ→←🧊 𝗣 = Σ≡p H refl where
  H : isPred (isProp🧊 {ℓ})
  H = subst isPred (sym $ funExt $ λ x → isProp≡🧊) isPredIsProp

ℙ←→🧊 : (𝗣 : ℙ ℓ) → ℙ←🧊 (ℙ→🧊 𝗣) ≡ 𝗣
ℙ←→🧊 𝗣 = Σ≡p isPredIsProp refl

ℙ≅🧊 : ℙ ℓ ≅ ℙ🧊 ℓ
ℙ≅🧊 = mk≅ ℙ→🧊 ℙ←🧊 ℙ→←🧊 ℙ←→🧊

ℙ≡🧊 : ℙ ℓ ≡ ℙ🧊 ℓ
ℙ≡🧊 = ua ℙ≅🧊

isSetℙ : isSet (ℙ ℓ)
isSetℙ = subst isSet ℙ≡🧊 (isSet←🧊 isSetHProp)

--------------------------------------------------------------------------------
-- Propositional extensionality

propExt : isProp A → isProp B → A ↔ B → A ≡ B
propExt pA pB iff = Eq←🧊 $ 🧊.hPropExt (isProp→🧊 pA) (isProp→🧊 pB) (iff .⇒) (iff .⇐)

propExt⁻ : A ≡ B → A ↔ B
propExt⁻ eq = subst (_↔ _) eq ↔-refl

ℙExt : 𝗣 holds ↔ 𝗤 holds → 𝗣 ≡ 𝗤
ℙExt {𝗣} {𝗤} H = Σ≡p isPredIsProp (propExt (isPredHolds 𝗣) (isPredHolds 𝗤) H)

ℙExt⁻ : 𝗣 ≡ 𝗤 → 𝗣 holds ↔ 𝗤 holds
ℙExt⁻ H = subst (λ - → - holds ↔ _) H ↔-refl

propTruncExt : A ↔ B → ∥ A ∥₁ ≡ ∥ B ∥₁
propTruncExt iff = ua $ mk≅ (𝟙.map $ iff .⇒) (𝟙.map $ iff .⇐) (λ _ → 𝟙.squash _ _) λ _ → 𝟙.squash _ _

--------------------------------------------------------------------------------
-- hProp truncation

∥_∥ₚ : 𝕋 ℓ → ℙ ℓ
∥ A ∥ₚ = ∥ A ∥₁ , 𝟙.squash

ℙTruncExt : A ↔ B → ∥ A ∥ₚ ≡ ∥ B ∥ₚ
ℙTruncExt iff = Σ≡p isPredIsProp (propTruncExt iff)
