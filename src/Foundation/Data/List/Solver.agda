module Foundation.Data.List.Solver where

open import Foundation.Prelude
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic

import Data.List.Membership.Setoid as Setoid
open import Reflection

open import Relation.Binary.Bundles using (Setoid)

private
  solve∈++-macro : Term → Term → TC ⊤
  solve∈++-macro H hole = do
    (def (quote Setoid._∈_) (hArg _ ∷ hArg ℓ ∷ vArg _ ∷ vArg x ∷ vArg xs ∷ [])) ← inferType hole
      where _ → typeError (strErr "not a membership relation" ∷ [])
    p ← buildProof x xs
    unify hole p
    where
    buildProof : Term → Term → TC Term
    buildProof x (def (quote _++_) (hArg ℓ ∷ hArg A ∷ vArg xs ∷ vArg ys ∷ [])) =
      let left  = def (quote ∈++-introˡ) (hArg ℓ ∷ hArg A ∷ hArg x ∷ hArg xs ∷ hArg ys ∷ vArg H ∷ [])
          right = def (quote ∈++-introʳ) (hArg ℓ ∷ hArg A ∷ hArg x ∷ hArg ys ∷ hArg xs ∷ vArg H ∷ [])
      in do
      ty ← inferType hole
      catchTC (checkType left ty) $ catchTC (checkType right ty)
        do  next ← buildProof x ys
            pure (def (quote ∈++-introʳ) (hArg ℓ ∷ hArg A ∷ hArg x ∷ hArg ys ∷ hArg xs ∷ vArg next ∷ []))
    buildProof _ _ = typeError (strErr "not a concatenation" ∷ [])

macro
  solve∈++ : Term → Term → TC ⊤
  solve∈++ = solve∈++-macro

private module Test (xs ys zs : 𝕃 ℕ) where
  test-solve∈++ : xs ⊆ xs ++ ys ++ zs
  test-solve∈++ H = solve∈++ H
