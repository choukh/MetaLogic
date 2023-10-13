module Foundation.Prelude.HLevel where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function
open import Foundation.Prelude.Equality

--------------------------------------------------------------------------------
-- Renaming 🧊

open import Cubical.Foundations.Prelude public
  using ()
  renaming (
    isProp to isProp🧊;
    isSet to isSet🧊
  )

open import Cubical.Foundations.Prelude
  using ()
  renaming (
    isProp→isSet to isProp→isSet🧊;
    isPropIsProp to isPropIsProp🧊
  )

open import Cubical.Foundations.HLevels
  using ()
  renaming (
    isPropΠ to isPropΠ🧊;
    isSetΠ  to isSetΠ🧊;
    isProp→ to isProp⇒🧊;
    isSet→  to isSet⇒🧊;
    isPropΣ to isPropΣ🧊;
    isSetΣ  to isSetΣ🧊;
    isPropIsSet to isPropIsSet🧊
  )

--------------------------------------------------------------------------------
-- Definition 1

isProp : 𝕋 ℓ → 𝕋 ℓ
isProp A = (x y : A) → x ＝ y

isPred : (A → 𝕋 ℓ) → 𝕋 _
isPred P = ∀ x → isProp (P x)

isPred🧊 : (A → 𝕋 ℓ) → 𝕋 _
isPred🧊 P = ∀ x → isProp🧊 (P x)

isPred2 : (∀ x → P x → 𝕋 ℓ) → 𝕋 _
isPred2 P₂ = ∀ x y → isProp (P₂ x y)

--------------------------------------------------------------------------------
-- Definition 2

isSet : 𝕋 ℓ → 𝕋 ℓ
isSet A = (x y : A) → isProp (x ＝ y)

isSets : (A → 𝕋 ℓ) → 𝕋 _
isSets P = ∀ x → isSet (P x)

isSets🧊 : (A → 𝕋 ℓ) → 𝕋 _
isSets🧊 P = ∀ x → isSet🧊 (P x)

--------------------------------------------------------------------------------
-- Mapping 1

open import Cubical.Data.Equality public
  using ()
  renaming (
    isPropToIsPropPath to isProp→🧊;
    isPropPathToIsProp to isProp←🧊
  )

mapIsProp : (isProp🧊 A → isProp🧊 B) → (isProp A → isProp B)
mapIsProp F = isProp←🧊 ∘ F ∘ isProp→🧊

isPred→🧊 : isPred P → isPred🧊 P
isPred→🧊 H x = isProp→🧊 (H x)

isPred←🧊 : isPred🧊 P → isPred P
isPred←🧊 H x = isProp←🧊 (H x)

--------------------------------------------------------------------------------
-- Mapping 2

isSet→🧊 : isSet A → isSet🧊 A
isSet→🧊 H x y = isProp→🧊 $ subst isProp (sym Eq＝🧊) (H x y)

isSet←🧊 : isSet🧊 A → isSet A
isSet←🧊 H x y = isProp←🧊 $ subst isProp🧊 Eq＝🧊 (H x y)

mapIsSet : (isSet🧊 A → isSet🧊 B) → (isSet A → isSet B)
mapIsSet F = isSet←🧊 ∘ F ∘ isSet→🧊

isSets→🧊 : isSets P → isSets🧊 P
isSets→🧊 H x = isSet→🧊 (H x)

isSets←🧊 : isSets🧊 P → isSets P
isSets←🧊 H x = isSet←🧊 (H x)

isProp→isSet : isProp A → isSet A
isProp→isSet pA = isSet←🧊 $ isProp→isSet🧊 $ isProp→🧊 pA

--------------------------------------------------------------------------------
-- Equiv

isProp＝🧊 : isProp A ＝ isProp🧊 A
isProp＝🧊 = EqΠ2 λ _ _ → Eq＝🧊

isSet＝🧊 : isSet A ＝ isSet🧊 A
isSet＝🧊 = EqΠ2 λ x y → subst (λ - → isProp - ＝ isProp🧊 (x ＝🧊 y)) Eq＝🧊 isProp＝🧊

isPredIsProp : isPred (isProp {ℓ})
isPredIsProp _ = isProp←🧊 (subst isProp🧊 isProp＝🧊 isPropIsProp🧊)

isPredIsSet : isPred (isSet {ℓ})
isPredIsSet _ = isProp←🧊 (subst isProp🧊 isSet＝🧊 isPropIsSet🧊)

--------------------------------------------------------------------------------
-- Π

isPropΠ : isPred P → isProp ((x : A) → P x)
isPropΠ H = isProp←🧊 $ isPropΠ🧊 $ isPred→🧊 H

isPropΠ2 : isPred2 P₂ → isProp ((x : A) (y : P x) → P₂ x y)
isPropΠ2 H = isPropΠ λ x → isPropΠ (H x)

isSetΠ : isSets P → isSet ((x : A) → P x)
isSetΠ H = isSet←🧊 $ isSetΠ🧊 $ isSets→🧊 H

--------------------------------------------------------------------------------
-- →

isProp→ : isProp B → isProp (A → B)
isProp→ = mapIsProp isProp⇒🧊

isSet→ : isSet B → isSet (A → B)
isSet→ = mapIsSet isSet⇒🧊

--------------------------------------------------------------------------------
-- Σ

isPropΣ : isProp A → isPred P → isProp (Σ A P)
isPropΣ pA pP = isProp←🧊 $ isPropΣ🧊 (isProp→🧊 pA) $ isPred→🧊 pP

isSetΣ : isSet A → isSets P → isSet (Σ A P)
isSetΣ sA sP = isSet←🧊 $ isSetΣ🧊 (isSet→🧊 sA) $ isSets→🧊 sP
