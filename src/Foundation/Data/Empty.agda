module Foundation.Data.Empty where

open import Foundation.Prelude

open import Data.Empty public
  using (⊥)
  renaming (⊥-elim to exfalso)

open import Data.Empty.Polymorphic public
  using ()
  renaming (⊥ to ⊥*; ⊥-elim to exfalso*)

open import Cubical.Data.Empty
  using ()
  renaming (
    ⊥ to ⊥🧊; isProp⊥ to isProp⊥🧊;
    ⊥* to ⊥*🧊; isProp⊥* to isProp⊥*🧊)

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

Empty*→🧊 : ⊥* {ℓ} → ⊥*🧊 {ℓ}
Empty*→🧊 ()

Empty*←🧊 : ⊥*🧊 {ℓ} → ⊥* {ℓ}
Empty*←🧊 ()

Empty*≅🧊 : ⊥* {ℓ} ≅ ⊥*🧊
Empty*≅🧊 = mk≅ Empty*→🧊 Empty*←🧊 (λ ()) (λ ())

Empty*＝🧊 : ⊥* {ℓ} ＝ ⊥*🧊
Empty*＝🧊 = ua Empty*≅🧊

isProp⊥* : isProp (⊥* {ℓ})
isProp⊥* = subst isProp Empty*＝🧊 (isProp←🧊 isProp⊥*🧊)

isSet* : isSet (⊥* {ℓ})
isSet* = isProp→isSet isProp⊥*
