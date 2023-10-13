module Foundation.Data.Empty where

open import Foundation.Prelude

open import Data.Empty public
  using (⊥)
  renaming (⊥-elim to exfalso)

open import Data.Empty.Polymorphic public
  using ()
  renaming (⊥ to ⊥*; ⊥-elim to exfalso*)

open import Cubical.Data.Empty
  renaming (⊥ to ⊥🧊; isProp⊥ to isProp⊥🧊)

Empty→🧊 : ⊥ → ⊥🧊
Empty→🧊 ()

Empty←🧊 : ⊥🧊 → ⊥
Empty←🧊 ()

Empty≅🧊 : ⊥ ≅ ⊥🧊
Empty≅🧊 = mk≅ Empty→🧊 Empty←🧊 (λ ()) (λ ())

Empty＝🧊 : ⊥ ＝ ⊥🧊
Empty＝🧊 = ua Empty≅🧊

isProp⊥ : isProp ⊥
isProp⊥ = subst isProp Empty＝🧊 (isProp←🧊 isProp⊥🧊)

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥
