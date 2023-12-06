module Foundation.Relation.Nullary.Discrete where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Decidable

open import Relation.Binary public
  using ()
  renaming (DecidableEquality to discrete)

open import Cubical.Relation.Nullary as 🧊
  using ()
  renaming (
    Discrete to discrete🧊;
    Discrete→isSet to discrete🧊→isSet🧊
  )

discrete→🧊 : discrete A → discrete🧊 A
discrete→🧊 H x y = Dec→🧊 $ subst Dec (sym Eq≡🧊) (H x y)

discrete←🧊 : discrete🧊 A → discrete A
discrete←🧊 H x y = Dec←🧊 $ subst 🧊.Dec Eq≡🧊 (H x y)

discrete→isSet : discrete A → isSet A
discrete→isSet = isSet←🧊 ∘ discrete🧊→isSet🧊 ∘ discrete→🧊

isPropDiscrete : isSet A → isProp (discrete A)
isPropDiscrete H = isPropΠ2 λ x y → isPropDec (H x y)

𝔻 : ∀ ℓ → 𝕋 (ℓ ⁺)
𝔻 ℓ = TypeWithStr ℓ discrete

𝔻₀ : 𝕋₁
𝔻₀ = 𝔻 ℓ0

isSetTyp𝔻 : {𝗔 : 𝔻 ℓ} → isSet (typ 𝗔)
isSetTyp𝔻 {𝗔} = discrete→isSet (str 𝗔)
