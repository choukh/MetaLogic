module Foundation.Logic.Prop where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Logic.Iff

open import Cubical.Foundations.HLevels public
  using ()
  renaming (hProp to Ω🧊)

open import Cubical.Foundations.HLevels
  using (isSetHProp)

import Cubical.Foundations.Univalence as 🧊

--------------------------------------------------------------------------------
-- hProp

Ω : ∀ ℓ → 𝕋 (ℓ ⁺)
Ω ℓ = TypeWithStr ℓ isProp

Ωₒ : 𝕋 (ℓ0 ⁺)
Ωₒ = Ω ℓ0

variable
  𝗣 𝗤 𝗥 : Ω ℓ

_holds : Ω ℓ → 𝕋 ℓ
_holds = typ

isPredHolds : isPred (_holds {ℓ})
isPredHolds = str

Ω→🧊 : Ω ℓ → Ω🧊 ℓ
Ω→🧊 (P , pP) = P , (isProp→🧊 pP)

Ω←🧊 : Ω🧊 ℓ → Ω ℓ
Ω←🧊 (P , pP) = P , (isProp←🧊 pP)

Ω→←🧊 : (𝗣 : Ω🧊 ℓ) → Ω→🧊 (Ω←🧊 𝗣) ＝ 𝗣
Ω→←🧊 𝗣 = SigEqProp H refl where
  H : isPred (isProp🧊 {ℓ})
  H = subst isPred (sym $ funExt $ λ x → isProp＝🧊) isPredIsProp

Ω←→🧊 : (𝗣 : Ω ℓ) → Ω←🧊 (Ω→🧊 𝗣) ＝ 𝗣
Ω←→🧊 𝗣 = SigEqProp isPredIsProp refl

Ω≅🧊 : Ω ℓ ≅ Ω🧊 ℓ
Ω≅🧊 = mk≅ Ω→🧊 Ω←🧊 Ω→←🧊 Ω←→🧊

Ω＝🧊 : Ω ℓ ＝ Ω🧊 ℓ
Ω＝🧊 = ua Ω≅🧊

isSetΩ : isSet (Ω ℓ)
isSetΩ = subst isSet Ω＝🧊 (isSet←🧊 isSetHProp)

--------------------------------------------------------------------------------
-- Propositional extensionality

propExt : isProp A → isProp B → (A ↔ B) → A ＝ B
propExt pA pB iff = Eq←🧊 $ 🧊.hPropExt (isProp→🧊 pA) (isProp→🧊 pB) (iff .⇒) (iff .⇐)

propExt⁻ : A ＝ B → (A ↔ B)
propExt⁻ eq = subst (_↔ _) eq ↔-refl

ΩExt : 𝗣 holds ↔ 𝗤 holds → 𝗣 ＝ 𝗤
ΩExt {𝗣} {𝗤} H = SigEqProp isPredIsProp (propExt (isPredHolds 𝗣) (isPredHolds 𝗤) H)

ΩExt⁻ : 𝗣 ＝ 𝗤 → 𝗣 holds ↔ 𝗤 holds
ΩExt⁻ H = subst (λ - → - holds ↔ _) H ↔-refl

propTruncExt : A ↔ B → ∥ A ∥₁ ＝ ∥ B ∥₁
propTruncExt iff = ua $ mk≅ (map1 $ iff .⇒) (map1 $ iff .⇐) (λ _ → is1 _ _) λ _ → is1 _ _

--------------------------------------------------------------------------------
-- hProp truncation

∥_∥ : 𝕋 ℓ → Ω ℓ
∥ A ∥ = ∥ A ∥₁ , is1

ΩTruncExt : A ↔ B → ∥ A ∥ ＝ ∥ B ∥
ΩTruncExt iff = SigEqProp isPredIsProp (propTruncExt iff)
 