module Foundation.Data.Unit where

open import Foundation.Prelude

open import Data.Unit.Polymorphic public
  using ()
  renaming (⊤ to ⊤*; tt to tt*)

isProp⊤ : isProp ⊤
isProp⊤ _ _ = refl

isProp⊤* : isProp (⊤* {ℓ})
isProp⊤* _ _ = refl

isSet⊤ : isSet ⊤
isSet⊤ _ _ refl refl = refl
