module Foundation.Functions.Surjection where

open import Foundation.Prelude

open import Cubical.Functions.Surjection public
  using ()
  renaming (isSurjection to surjective)

_↠_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ↠ B = Σ (A → B) surjective
