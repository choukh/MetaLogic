module Foundation.Prelude.HLevel where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function

open import Cubical.Data.Equality public
  using (isProp)
  renaming (
    isPropToIsPropPath to isProp→🧊;
    isPropPathToIsProp to isProp←🧊
  )

open import Cubical.Foundations.Prelude
  using ()
  renaming (isProp to isProp🧊)

open import Cubical.Foundations.HLevels
  using ()
  renaming (
    isPropΠ to isPropΠ🧊
  )

private variable
  P : A → 𝒰 ℓ

isPred : (A → 𝒰 ℓ) → 𝒰 _
isPred P = ∀ x → isProp (P x)

mapIsProp : (isProp🧊 A → isProp🧊 B) → (isProp A → isProp B)
mapIsProp F = isProp←🧊 ∘ F ∘ isProp→🧊

isPropΠ : ((x : A) → isProp (P x)) → isProp ((x : A) → P x)
isPropΠ H = isProp←🧊 $ isPropΠ🧊 $ isProp→🧊 ∘ H
