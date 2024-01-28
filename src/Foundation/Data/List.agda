module Foundation.Data.List where

open import Foundation.Prelude
open import Foundation.Data.Sigma

open import Data.List public
  using (map; _++_; foldr; concat; length; [_]; filter)

open import Data.List.Properties public
  using (
    length-map; map-id; map-∘;
    length-++; ++-assoc; ++-identityʳ;
    foldr-preservesᵒ
  )

open import Cubical.Data.List
  using (isOfHLevelList)

open import Foundation.Data.Maybe
open import Data.Nat.Properties
  using (+-assoc)
open import Foundation.Data.Nat.AlternativeOrder

isSet𝕃 : isSet A → isSet (𝕃 A)
isSet𝕃 = mapIsSet (isOfHLevelList 0)

--------------------------------------------------------------------------------
-- _[_]?

_[_]? : 𝕃 A → ℕ → A ？
(x ∷ _)  [ zero ]?  = some x
(_ ∷ xs) [ suc n ]? = xs [ n ]?
_ [ _ ]? = none

Σ[<length]? : (xs : 𝕃 A) {n : ℕ} → n < length xs → Σ x ， xs [ n ]? ≡ some x
Σ[<length]? (x ∷ xs) {n = zero} _ = x , refl
Σ[<length]? (x ∷ xs) {suc n} lt = Σ[<length]? xs (+-cancelˡ-≤ _ _ _ lt)

++[]? : (xs : 𝕃 A) {ys : 𝕃 A} {x : A} {n : ℕ} →
             xs [ n ]? ≡ some x → (xs ++ ys) [ n ]? ≡ some x
++[]? (x ∷ xs) {n = zero} = id
++[]? (x ∷ xs) {n = suc n} = ++[]? xs

--------------------------------------------------------------------------------
-- _[_]⁻¹!

_[_]⁻¹! : (xs : 𝕃 A) {n : ℕ} → n < length xs → A
xs [ le ]⁻¹! = Σ[<length]? xs le .fst

_[_]⁻¹!≡ : (xs : 𝕃 A) {n : ℕ} (le : n < length xs) → xs [ n ]? ≡ some (xs [ le ]⁻¹!)
xs [ le ]⁻¹!≡ = Σ[<length]? xs le .snd

--------------------------------------------------------------------------------
-- misc

length-++-++ : ∀ (xs ys : 𝕃 A) {zs} →
  length (xs ++ ys ++ zs) ≡ length xs + length ys + length zs
length-++-++ xs ys {zs} =
  length (xs ++ ys ++ zs)             ≡⟨ length-++ xs ⟩
  length xs + length (ys ++ zs)       ≡⟨ cong (length xs +_) (length-++ ys) ⟩
  length xs + (length ys + length zs) ≡˘⟨ +-assoc (length xs) _ _ ⟩
  length xs + length ys + length zs   ∎
