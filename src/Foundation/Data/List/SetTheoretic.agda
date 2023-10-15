module Foundation.Data.List.SetTheoretic where

open import Data.List.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.List.Relation.Binary.Subset.Propositional public
  using (_⊆_)
open import Data.List.Membership.Propositional.Properties public
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there)
