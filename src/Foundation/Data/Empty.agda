module Foundation.Data.Empty where

open import Foundation.Prelude

open import Data.Empty public
  using (⊥)
  renaming (⊥-elim to exfalso)

open import Cubical.Data.Empty
  renaming (⊥ to ⊥🧊; isProp⊥ to isProp⊥🧊)

⊥→🧊 : ⊥ → ⊥🧊
⊥→🧊 ()

⊥←🧊 : ⊥🧊 → ⊥
⊥←🧊 ()

⊥≅🧊 : ⊥ ≅ ⊥🧊
⊥≅🧊 = mk≅ ⊥→🧊 ⊥←🧊 (λ ()) (λ ())

⊥＝🧊 : ⊥ ＝ ⊥🧊
⊥＝🧊 = ua ⊥≅🧊

isProp⊥ : isProp ⊥
isProp⊥ = subst isProp ⊥＝🧊 (isProp←🧊 isProp⊥🧊)

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥
