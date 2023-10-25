module Foundation.Set.Powerset where

open import Foundation.Prelude
open import Foundation.Logic

import Cubical.Foundations.Powerset as 🧊

𝒫 : 𝕋 ℓ → 𝕋 (ℓ ⁺)
𝒫 X = X → ℙ _
