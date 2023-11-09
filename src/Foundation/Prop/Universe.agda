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

ℙₒ : 𝕋 (ℓ0 ⁺)
ℙₒ = ℙ ℓ0

variable
  𝗣 𝗤 𝗥 : ℙ ℓ

_holds : ℙ ℓ → 𝕋 ℓ
_holds = typ

isPredHolds : isPred (_holds {ℓ})
isPredHolds = str

--------------------------------------------------------------------------------
-- Instance

⊥ₚ : ℙₒ
⊥ₚ = ⊥ , isProp⊥

⊤ₚ : ℙₒ
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

propExt : isProp A → isProp B → (A ↔ B) → A ≡ B
propExt pA pB iff = Eq←🧊 $ 🧊.hPropExt (isProp→🧊 pA) (isProp→🧊 pB) (iff .⇒) (iff .⇐)

propExt⁻ : A ≡ B → (A ↔ B)
propExt⁻ eq = subst (_↔ _) eq ↔-refl

ℙExt : 𝗣 holds ↔ 𝗤 holds → 𝗣 ≡ 𝗤
ℙExt {𝗣} {𝗤} H = Σ≡p isPredIsProp (propExt (isPredHolds 𝗣) (isPredHolds 𝗤) H)

ℙExt⁻ : 𝗣 ≡ 𝗤 → 𝗣 holds ↔ 𝗤 holds
ℙExt⁻ H = subst (λ - → - holds ↔ _) H ↔-refl

propTruncExt : A ↔ B → ∥ A ∥₁ ≡ ∥ B ∥₁
propTruncExt iff = ua $ mk≅ (map1 $ iff .⇒) (map1 $ iff .⇐) (λ _ → is1 _ _) λ _ → is1 _ _

--------------------------------------------------------------------------------
-- hProp truncation

∥_∥ : 𝕋 ℓ → ℙ ℓ
∥ A ∥ = ∥ A ∥₁ , is1

ℙTruncExt : A ↔ B → ∥ A ∥ ≡ ∥ B ∥
ℙTruncExt iff = Σ≡p isPredIsProp (propTruncExt iff)
