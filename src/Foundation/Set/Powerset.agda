module Foundation.Set.Powerset where

open import Foundation.Prelude
open import Foundation.Prop.Universe

import Cubical.Foundations.Powerset as 🧊

𝒫 : 𝕋 ℓ → 𝕋 (ℓ ⁺)
𝒫 X = X → ℙ _

isSet𝒫 : isSet (𝒫 X)
isSet𝒫 = isSet→ isSetℙ

_∈_ : T → 𝒫 T → 𝕋 _
x ∈ A = A x holds

isProp∈ : {x : X} {A : 𝒫 X} → isProp (x ∈ A)
isProp∈ {x} {A} = isPredHolds (A x)
