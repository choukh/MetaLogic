module Foundation.Function.Isomorphism where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function
open import Foundation.Prelude.Equality
open import Foundation.Prelude.HLevel
open import Foundation.Data.Sigma

open import Cubical.Foundations.Isomorphism as 🧊
  using (Iso)

open import Cubical.Foundations.Equiv as 🧊
  using (isPropIsEquiv)

import Cubical.Foundations.Univalence as 🧊

import Function as ⓢ
open Iso

--------------------------------------------------------------------------------
-- Stdlib Conversion

Iso→ⓢ : A ≅ B → A ⓢ.↔ B
Iso→ⓢ (mk≅ fun inv rightInv leftInv) = ⓢ.mk↔ {to = fun} {from = inv} $
  (λ eq → subst (λ - → fun - ≡ _) eq (rightInv _)) ,
  (λ eq → subst (λ - → inv - ≡ _) eq (leftInv _))

Iso←ⓢ : A ⓢ.↔ B → A ≅ B
Iso←ⓢ record { to = f ; from = g ; to-cong = f-cong ; from-cong = g-cong ; inverse = r , l } =
  mk≅ f g (λ _ → r refl) (λ _ → l refl)

Iso→←ⓢ : isSet A → isSet B → (H : A ⓢ.↔ B) → Iso→ⓢ (Iso←ⓢ H) ≡ H
Iso→←ⓢ {A} {B} sA sB record { to = f ; from = g ; to-cong = f-cong ; from-cong = g-cong ; inverse = r , l } =
  subst2 (λ x y → _ ≡ record { to-cong = x ; from-cong = y })
    (isProp-f-cong (cong f) f-cong) (isProp-g-cong (cong g) g-cong) $
      subst (λ x → lhs ≡ record { inverse = x })
        (×≡ (isProp-r r _) (isProp-l l _)) refl
  where
  lhs : A ⓢ.↔ B
  lhs = record { inverse = (λ eq → subst (λ - → f - ≡ _) eq (r refl)) , (λ eq → subst (λ - → g - ≡ _) eq (l refl)) }
  isProp-f-cong : isProp (∀ {x y} → x ≡ y → f x ≡ f y)
  isProp-f-cong = isPropΠ₋2 λ _ _ → isProp→ (sB _ _)
  isProp-g-cong : isProp (∀ {x y} → x ≡ y → g x ≡ g y)
  isProp-g-cong = isPropΠ₋2 λ _ _ → isProp→ (sA _ _)
  isProp-r : isProp (∀ {x y} → y ≡ g x → f y ≡ x)
  isProp-r = isPropΠ₋2 λ _ _ → isProp→ (sB _ _)
  isProp-l : isProp (∀ {x y} → y ≡ f x → g y ≡ x)
  isProp-l = isPropΠ₋2 λ _ _ → isProp→ (sA _ _)

Iso←→ⓢ : (H : A ≅ B) → Iso←ⓢ (Iso→ⓢ H) ≡ H
Iso←→ⓢ (mk≅ fun inv rightInv leftInv) = refl

Iso≅ⓢ : isSet A → isSet B → (A ≅ B) ≅ (A ⓢ.↔ B)
Iso≅ⓢ sA sB = mk≅ Iso→ⓢ Iso←ⓢ (Iso→←ⓢ sA sB) Iso←→ⓢ

Iso≡ⓢ : isSet A → isSet B → (A ≅ B) ≡ (A ⓢ.↔ B)
Iso≡ⓢ sA sB = ua $ Iso≅ⓢ sA sB

--------------------------------------------------------------------------------
-- Properties

idIso : A ≅ A
idIso = mk≅ id id (λ _ → refl) (λ _ → refl)

invIso : A ≅ B → B ≅ A
invIso i = mk≅ (i .inv) (i .fun) (i .leftInv) (i .rightInv)

compIso : A ≅ B → B ≅ C → A ≅ C
compIso i j = mk≅ (fun j ∘ fun i) (inv i ∘ inv j)
  (λ b → cong (fun j) (rightInv i (inv j b)) ∙ rightInv j b)
  (λ a → cong (inv i) (leftInv j (fun i a)) ∙ leftInv i a)

infixr 0 _≅⟨_⟩_ _≅˘⟨_⟩_
_≅⟨_⟩_ : {B : 𝕋 ℓ′} {C : 𝕋 ℓ″} (X : 𝕋 ℓ) → X ≅ B → B ≅ C → X ≅ C
_ ≅⟨ f ⟩ g = compIso f g

_≅˘⟨_⟩_ : {B : 𝕋 ℓ′} {C : 𝕋 ℓ″} (X : 𝕋 ℓ) → B ≅ X → B ≅ C → X ≅ C
_ ≅˘⟨ f ⟩ g = compIso (invIso f) g

infix 1 _≅∎
_≅∎ : (A : 𝕋 ℓ) → A ≅ A
A ≅∎ = idIso {A = A}

--------------------------------------------------------------------------------
-- Univalence

Iso🧊≅Equiv🧊 : isSet A → (A ≅🧊 B) ≅ (A ≃🧊 B)
Iso🧊≅Equiv🧊 sA = mk≅ 🧊.isoToEquiv 🧊.equivToIso right (Eq←🧊 ∘ left) where
  right : ∀ equiv → 🧊.isoToEquiv (🧊.equivToIso equiv) ≡ equiv
  right _ = Σ≡p (λ _ → isProp←🧊 $ isPropIsEquiv _) refl
  left : ∀ iso → 🧊.equivToIso (🧊.isoToEquiv iso) ≡🧊 iso
  fun (left iso i) = iso .fun
  inv (left iso i) = iso .inv
  rightInv (left iso i) = iso .rightInv
  leftInv (left iso i) y = H i where
    H : 🧊.retEq (🧊.isoToEquiv iso) y ≡🧊 leftInv iso y
    H = isSet→🧊 sA (iso .inv (iso .fun y)) _ _ _

Iso≅Equiv🧊 : isSet A → (A ≅ B) ≅ (A ≃🧊 B)
Iso≅Equiv🧊 {A} {B} sA =
  A ≅ B   ≅⟨ Iso≅🧊 ⟩
  A ≅🧊 B ≅⟨ Iso🧊≅Equiv🧊 sA ⟩
  A ≃🧊 B ≅∎

univalence : isSet A → (A ≡ B) ≅ (A ≅ B)
univalence {A} {B} sA =
  A ≡ B ≅⟨ Eq≅🧊 ⟩
  A ≡🧊 B ≅⟨ Iso←🧊 🧊.univalenceIso ⟩
  A ≃🧊 B ≅˘⟨ Iso≅Equiv🧊 sA ⟩
  A ≅ B ≅∎
