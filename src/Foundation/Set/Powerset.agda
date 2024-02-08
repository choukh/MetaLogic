{-# OPTIONS --lossy-unification #-}
module Foundation.Set.Powerset where

open import Foundation.Prelude
  hiding (A; B; C)
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Prop.Universe
open import Foundation.Data.Sigma
open import Foundation.Data.Sum
open import Foundation.Relation.Nullary.Negation

import Cubical.Foundations.Powerset as 🧊

------------------------------------------------------------------------
-- Definition

𝒫 : 𝕋 ℓ → 𝕋 (ℓ ⁺)
𝒫 X = X → ℙ _

isSet𝒫 : isSet (𝒫 X)
isSet𝒫 = isSet→ isSetℙ

------------------------------------------------------------------------
-- Membership

infix 5 _∈_ _∉_ _∈ₚ_ _⊆_

_∈_ : X → 𝒫 X → 𝕋 _
x ∈ A = A x holds

_∉_ : X → 𝒫 X → 𝕋 _
x ∉ A = ¬ (A x holds)

isProp∈ : {x : X} {A : 𝒫 X} → isProp (x ∈ A)
isProp∈ {x} {A} = isPredHolds (A x)

_∈ₚ_ : X → 𝒫 X → ℙ _
x ∈ₚ A = x ∈ A , isProp∈

------------------------------------------------------------------------
-- Subset

private variable
  A B C : 𝒫 X
  x : X

_⊆_ : 𝒫 X → 𝒫 X → 𝕋 _
A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

isProp⊆ : isProp (A ⊆ B)
isProp⊆ {A} {B} = isPropΠ̅ $ λ _ → isPropΠ λ _ → isProp∈ {A = B}

⊆-refl : A ⊆ A
⊆-refl = id

⊆-trans : A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A⊆B B⊆C x∈A = B⊆C $ A⊆B x∈A

⊆-extensionality : (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality (p , q) = funExt λ x → ℙExt (⇒: p ⇐: q)

⊆-antisym : A ⊆ B → B ⊆ A → A ≡ B
⊆-antisym A⊆B B⊆A = ⊆-extensionality $ A⊆B , B⊆A

⊆-extensionality⁻ : A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-extensionality⁻ {A} {B} refl = ⊆-refl {A = A} , ⊆-refl {A = B}

⊆-extensionalityEquiv : (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv {A} {B} = Iso→Equiv $ mk≅ ⊆-extensionality ⊆-extensionality⁻
  (λ _ → isSet𝒫 _ _ _ _)
  (λ _ → isPropΣ (isProp⊆ {A = A} {B = B}) (λ _ → isProp⊆ {A = B} {B = A}) _ _)

------------------------------------------------------------------------
-- Operations on sets

-- Union

_∪_ : 𝒫 X → 𝒫 X → 𝒫 X
A ∪ B = λ x → x ∈ A ∨ x ∈ B , 𝟙.squash

-- Big union

module _ {X Y : 𝕋 ℓ} (Aᵢ : X → 𝒫 Y) where

  ⋃ᵢ : 𝒫 Y
  ⋃ᵢ = λ y → (∃ x ， y ∈ Aᵢ x) , 𝟙.squash

  ⊆⋃ᵢ : Aᵢ x ⊆ ⋃ᵢ
  ⊆⋃ᵢ {x} = ex x

module SetOperation (Xset : isSet X) where

  -- Singleton set

  ｛_｝ : X → 𝒫 X
  ｛ x ｝ = λ y → x ≡ y , Xset x y

  -- Incusion

  infixl 6 _⨭_
  _⨭_ : (A : 𝒫 X) (x : X) → 𝒫 X
  A ⨭ x = A ∪ ｛ x ｝

  ⨭⊆⨭ : A ⊆ B → A ⨭ x ⊆ B ⨭ x
  ⨭⊆⨭ A⊆B = 𝟙.rec isProp∈
    λ { (inj₁ H) → inl (A⊆B H)
      ; (inj₂ H) → inr H
      }
