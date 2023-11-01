module Foundation.Data.Vec.SetTheoretic where

open import Foundation.Prelude
open import Foundation.Data.Vec

open import Data.Vec.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.Vec.Relation.Unary.Any public
  using (Any; here; there)

private variable
  n : ℕ
  t⃗ : 𝕍 A n
  f g : A → B

map-ext : (∀ t → t ∈ t⃗ → f t ≡ g t) → map⃗ f t⃗ ≡ map⃗ g t⃗
map-ext {t⃗ = []} H = refl
map-ext {t⃗ = t ∷ t⃗} H = cong2 _∷_ (H t $ here refl) (map-ext λ s s∈t⃗ → H s $ there s∈t⃗)
