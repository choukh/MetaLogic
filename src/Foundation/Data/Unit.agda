module Foundation.Data.Unit where

open import Foundation.Prelude

isProp⊤ : isProp ⊤
isProp⊤ _ _ = refl

isSet⊤ : isSet ⊤
isSet⊤ _ _ refl refl = refl
