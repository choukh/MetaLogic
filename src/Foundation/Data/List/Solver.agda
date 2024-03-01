module Foundation.Data.List.Solver where

open import Foundation.Prelude
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic

import Data.List.Membership.Setoid as Setoid
open import Reflection

private
  solve∈++-macro : Term → Term → TC ⊤
  solve∈++-macro H hole = do
    ty@(def (quote Setoid._∈_) (hArg _ ∷ hArg _ ∷ vArg _ ∷ vArg x ∷ vArg xs ∷ [])) ← inferType hole
      where _ → typeError (strErr "not a membership relation" ∷ [])
    p ← buildProof x xs ty
    unify hole p
    where
    buildProof : Term → Term → Term → TC Term
    buildProof x (def (quote _++_) (hArg ℓ ∷ hArg A ∷ vArg xs ∷ vArg ys ∷ [])) ty =
      let left  = def (quote ∈++-introˡ) (hArg ℓ ∷ hArg A ∷ hArg x ∷ hArg xs ∷ hArg ys ∷ vArg H ∷ [])
          right = def (quote ∈++-introʳ) (hArg ℓ ∷ hArg A ∷ hArg x ∷ hArg ys ∷ hArg xs ∷ vArg H ∷ [])
      in catchTC (checkType left ty)
       $ catchTC (checkType right ty)
      do next ← buildProof x ys (def (quote _∈_) (hArg ℓ ∷ hArg A ∷ vArg x ∷ vArg ys ∷ []))
         pure (def (quote ∈++-introʳ) (hArg ℓ ∷ hArg A ∷ hArg x ∷ hArg ys ∷ hArg xs ∷ vArg next ∷ []))
    buildProof _ _ _ = typeError (strErr "sublist not found" ∷ [])

macro
  solve∈++ : Term → Term → TC ⊤
  solve∈++ = solve∈++-macro

private module Test (xs ys zs : 𝕃 ℕ) where
  test-solve∈++-0 : xs ⊆ xs ++ ys ++ zs
  test-solve∈++-0 H = solve∈++ H

  test-solve∈++-1 : ys ⊆ xs ++ ys ++ zs
  test-solve∈++-1 H = solve∈++ H

  test-solve∈++-2 : zs ⊆ xs ++ ys ++ zs
  test-solve∈++-2 H = solve∈++ H
