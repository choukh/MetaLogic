module Foundation.Data.List.SetTheoretic where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Function.Bundles
open import Foundation.Data.List

open import Data.List.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties public
  using (∈-++⁺ˡ; ∈-++⁺ʳ; map-∈↔)
open import Data.List.Relation.Binary.Subset.Propositional public
  using (_⊆_)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there)

∈map-intro : ∀ {f : A → B} {y xs} → (Σ x ⸴ x ∈ xs ∧ y ＝ f x) → y ∈ map f xs
∈map-intro {f} = Iso←ⓢ (map-∈↔ f) .fun

infixr 6 _[×]_
_[×]_ : 𝕃 A → 𝕃 B → 𝕃 (A × B)
[] [×] ys = []
(x ∷ xs) [×] ys = map (x ,_) ys ++ xs [×] ys

∈[×]-intro : ∀ {x y} {xs : 𝕃 A} {ys : 𝕃 B} → x ∈ xs → y ∈ ys → (x , y) ∈ xs [×] ys
∈[×]-intro {xs = _ ∷ xs} (here refl) y∈ = ∈-++⁺ˡ $ ∈map-intro $ _ , y∈ , refl
∈[×]-intro {xs = _ ∷ xs} (there x∈)  y∈ = ∈-++⁺ʳ _ $ ∈[×]-intro x∈ y∈
