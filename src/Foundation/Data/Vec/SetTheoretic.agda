module Foundation.Data.Vec.SetTheoretic where

open import Foundation.Prelude
open import Foundation.Data.Vec

open import Data.Vec.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.Vec.Relation.Unary.Any public
  using (Any; here; there)
