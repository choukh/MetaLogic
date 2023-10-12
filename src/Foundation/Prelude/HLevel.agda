module Foundation.Prelude.HLevel where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function
open import Foundation.Prelude.Equality

open import Cubical.Data.Equality public
  using ()
  renaming (
    isPropToIsPropPath to isProp→🧊;
    isPropPathToIsProp to isProp←🧊
  )

open import Cubical.Foundations.Prelude public
  using ()
  renaming (
    isProp to isProp🧊;
    isSet to isSet🧊
  )

open import Cubical.Foundations.HLevels public
  using ()
  renaming (
    isPropΠ to isPropΠ🧊;
    isSetΠ to isSetΠ🧊
  )

isProp : 𝕋 ℓ → 𝕋 ℓ
isProp A = (x y : A) → x ＝ y

isPred : (A → 𝕋 ℓ) → 𝕋 _
isPred P = ∀ x → isProp (P x)

mapIsProp : (isProp🧊 A → isProp🧊 B) → (isProp A → isProp B)
mapIsProp F = isProp←🧊 ∘ F ∘ isProp→🧊

isPropΠ : ((x : A) → isProp (P x)) → isProp ((x : A) → P x)
isPropΠ H = isProp←🧊 $ isPropΠ🧊 $ isProp→🧊 ∘ H

isPropΠ2 : ((x : A) (y : P x) → isProp (P₂ x y)) → isProp ((x : A) (y : P x) → P₂ x y)
isPropΠ2 H = isPropΠ λ x → isPropΠ (H x)

isSet : 𝕋 ℓ → 𝕋 ℓ
isSet A = (x y : A) → isProp (x ＝ y)

isSet→🧊 : isSet A → isSet🧊 A
isSet→🧊 H x y = isProp→🧊 $ subst isProp ⥱＝＝ (H x y)

isSet←🧊 : isSet🧊 A → isSet A
isSet←🧊 H x y = isProp←🧊 $ subst isProp🧊 (sym ⥱＝＝) (H x y)

mapIsSet : (isSet🧊 A → isSet🧊 B) → (isSet A → isSet B)
mapIsSet F = isSet←🧊 ∘ F ∘ isSet→🧊

isSetΠ : ((x : A) → isSet (P x)) → isSet ((x : A) → P x)
isSetΠ H = isSet←🧊 $ isSetΠ🧊 $ isSet→🧊 ∘ H
