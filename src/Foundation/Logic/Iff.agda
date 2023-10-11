module Foundation.Logic.Iff where

open import Foundation.Prelude.Builtin

--------------------------------------------------------------------------------
-- Bi-implication (iff) of Type (which has a seperate proof of prop-hood)

infix 3 _↔_
record _↔_ (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  field
    ⇒ : A → B
    ⇐ : B → A

open _↔_ public
