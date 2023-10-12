module Foundation.Relation.Nullary.Discrete where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Decidable

open import Cubical.Relation.Nullary
  using ()
  renaming (
    Discrete to discrete🧊;
    Discrete→isSet to discrete🧊→isSet🧊
  )

discrete : 𝕋 ℓ → 𝕋 ℓ
discrete A = (x y : A) → Dec (x ＝ y)

discrete→🧊 : discrete A → discrete🧊 A
discrete→🧊 H x y = Dec→🧊 $ subst Dec ⥱＝＝ (H x y)

discrete→isSet : discrete A → isSet A
discrete→isSet = isSet←🧊 ∘ discrete🧊→isSet🧊 ∘ discrete→🧊

isPropDiscrete : isSet A → isProp (discrete A)
isPropDiscrete H = isPropΠ2 λ x y → isPropDec (H x y)
