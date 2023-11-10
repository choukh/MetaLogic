module Foundation.Set.Universe where

open import Foundation.Prelude

open import Cubical.Foundations.HLevels public
  using ()
  renaming (hSet to 𝕊🧊)

--------------------------------------------------------------------------------
-- hSet

𝕊 : ∀ ℓ → 𝕋 (ℓ ⁺)
𝕊 ℓ = TypeWithStr ℓ isSet

𝕊₀ : 𝕋 (ℓ0 ⁺)
𝕊₀ = 𝕊 ℓ0

variable
  𝗔 𝗕 𝗖 : 𝕊 ℓ
