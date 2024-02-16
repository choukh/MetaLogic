module Foundation.Data.List.+Powerset where

open import Foundation.Prelude
open import Foundation.Prop.Truncation
open import Foundation.Set.Powerset
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈͆_; _∈₁_ to _∈͆₁_)

set : 𝕃 X → 𝒫 X
set xs = λ x → x ∈͆₁ xs , 𝟙.squash

infix 4 _⊆͆ₚ_
_⊆͆ₚ_ : 𝕃 X → 𝒫 X → 𝕋 _
xs ⊆͆ₚ A = ∀ {x} → x ∈͆ xs → x ∈ A
