module Foundation.Set.Powerset+List where

open import Foundation.Prelude
open import Foundation.Set.Powerset
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)

_ᴸ⊆ᴾ_ : 𝕃 X → 𝒫 X → 𝕋 _
xs ᴸ⊆ᴾ A = ∀ {x} → x ∈ᴸ xs → x ∈ A
