module Foundation.Logic.Iff where

open import Foundation.Prelude.Builtin

--------------------------------------------------------------------------------
-- Bi-implication (iff) of Type (which has a seperate proof of prop-hood)

infix 3 _↔_
record _↔_ (A : 𝕋 ℓ) (B : 𝕋 ℓ′) : 𝕋 (ℓ ⊔ ℓ′) where
  field
    ⇒ : A → B
    ⇐ : B → A

open _↔_ public
