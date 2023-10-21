module Foundation.Set.Powerset where

open import Foundation.Prelude
open import Foundation.Logic

import Cubical.Foundations.Powerset as 🧊

ℙ : 𝕋 ℓ → 𝕋 (ℓ ⁺)
ℙ X = X → Ω _
