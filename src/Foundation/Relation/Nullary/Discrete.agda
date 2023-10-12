module Foundation.Relation.Nullary.Discrete where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Decidable

open import Relation.Binary public
  using ()
  renaming (DecidableEquality to discrete)

open import Cubical.Relation.Nullary
  using ()
  renaming (
    Dec to Dec🧊;
    Discrete to discrete🧊;
    Discrete→isSet to discrete🧊→isSet🧊
  )

discrete→🧊 : discrete A → discrete🧊 A
discrete→🧊 H x y = Dec→🧊 $ subst Dec (sym Eq＝🧊) (H x y)

discrete←🧊 : discrete🧊 A → discrete A
discrete←🧊 H x y = Dec←🧊 $ subst Dec🧊 Eq＝🧊 (H x y)

discrete→isSet : discrete A → isSet A
discrete→isSet = isSet←🧊 ∘ discrete🧊→isSet🧊 ∘ discrete→🧊

isPropDiscrete : isSet A → isProp (discrete A)
isPropDiscrete H = isPropΠ2 λ x y → isPropDec (H x y)
