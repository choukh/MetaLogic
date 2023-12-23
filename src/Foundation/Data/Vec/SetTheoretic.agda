module Foundation.Data.Vec.SetTheoretic where

open import Foundation.Prelude
open import Foundation.Data.Vec

open import Data.Vec.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.Vec.Relation.Unary.Any public
  using (Any; here; there)

private variable
  n : ℕ
  x⃗ : 𝕍 A n
  f g : A → B

map-ext : (∀ x → x ∈ x⃗ → f x ≡ g x) → map⃗ f x⃗ ≡ map⃗ g x⃗
map-ext {x⃗ = []} H = refl
map-ext {x⃗ = x ∷ x⃗} H = cong2 _∷_ (H x $ here refl) (map-ext λ y y∈x⃗ → H y $ there y∈x⃗)
