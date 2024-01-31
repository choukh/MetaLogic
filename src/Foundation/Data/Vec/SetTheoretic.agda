module Foundation.Data.Vec.SetTheoretic where

open import Foundation.Prelude
open import Foundation.Data.Sigma
open import Foundation.Data.Vec

open import Data.Vec.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.Vec.Relation.Unary.Any public
  using (Any; here; there)

private variable
  n : ℕ
  x y : A
  x⃗ : 𝕍 A n
  f g : A → B

∈map⃗-intro : x ∈ x⃗ → f x ∈ map⃗ f x⃗
∈map⃗-intro (here refl)  = here refl
∈map⃗-intro (there H) = there (∈map⃗-intro H)

∈map⃗-elim : y ∈ map⃗ f x⃗ → Σ x ， x ∈ x⃗ × y ≡ f x
∈map⃗-elim {x⃗ = x ∷ x⃗} (here refl) = x , here refl , refl
∈map⃗-elim {x⃗ = _ ∷ x⃗} (there H) with ∈map⃗-elim H
... | x , x∈ , refl = x , there x∈ , refl

map⃗⊆P : (∀ x → x ∈ x⃗ → P (f x)) → ∀ y → y ∈ map⃗ f x⃗ → P y
map⃗⊆P {P} H y y∈ with ∈map⃗-elim y∈
... | x , x∈xs , y≡fx = subst P y≡fx $ H x x∈xs

map⃗-ext : (∀ x → x ∈ x⃗ → f x ≡ g x) → map⃗ f x⃗ ≡ map⃗ g x⃗
map⃗-ext {x⃗ = []} H = refl
map⃗-ext {x⃗ = x ∷ x⃗} H = cong2 _∷_ (H x $ here refl) (map⃗-ext λ y y∈x⃗ → H y $ there y∈x⃗)
