module Foundation.Relation.Binary.Core where

open import Foundation.Prelude
open import Relation.Binary.Core public
  renaming (Rel to Rel*)

Rel : 𝕋 → 𝕋₁
Rel A = Rel* A ℓ0
