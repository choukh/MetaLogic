module Foundation.Relation.Nullary.Discrete where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Decidable

open import Cubical.Relation.Nullary
  using ()
  renaming (Discrete to discrete🧊)

discrete : 𝒰 ℓ → 𝒰 ℓ
discrete A = (x y : A) → Dec (x ＝ y)

discrete→🧊 : discrete A → discrete🧊 A
discrete→🧊 H x y with H x y
... | yes p = Dec→🧊 $ yes $ ＝→⥱ p
... | no ¬p = Dec→🧊 $ no $ ¬p ∘ ＝←⥱
