module Foundation.Function.Bundles where

open import Foundation.Prelude
open import Foundation.Logic.Iff
open import Foundation.Logic.Prop
open import Foundation.Data.Sigma

open import Function public
  using (_↣_; _↠_)

open import Function as ⓢ
  using (
    _⇔_; mk⇔;
    Injective; Surjective
  )

open ⓢ.Equivalence

injective : (A → B) → 𝕋 _
injective = Injective _≡_ _≡_

surjective : (A → B) → 𝕋 _
surjective = Surjective _≡_ _≡_

mk↣ : (f : A → B) → injective f → A ↣ B
mk↣ f = ⓢ.mk↣

mk↠ : (f : A → B) → surjective f → A ↠ B
mk↠ f = ⓢ.mk↠

Iff→ⓢ : A ↔ B → A ⇔ B
Iff→ⓢ (⇒: ⇒ ⇐: ⇐) = mk⇔ ⇒ ⇐

Iff←ⓢ : A ⇔ B → A ↔ B
Iff←ⓢ H = ⇒: H .to ⇐: H .from

isProp⇔ : isProp A → isProp B → isProp (A ⇔ B)
isProp⇔ {A} {B} pA pB
  record { to = f₁ ; from = g₁ ; to-cong = f-cong₁ ; from-cong = g-cong₁ }
  record { to = f₂ ; from = g₂ ; to-cong = f-cong₂ ; from-cong = g-cong₂ }
  with isProp→ pB f₁ f₂ | isProp→ pA g₁ g₂
... | refl | refl = subst2 (λ x y → _ ≡ record { to-cong = x ; from-cong = y })
  (isProp-f-cong f-cong₁ f-cong₂) (isProp-g-cong g-cong₁ g-cong₂) refl
  where
  isProp-f-cong : isProp (∀ {x y} → x ≡ y → f₁ x ≡ f₁ y)
  isProp-f-cong = isPropΠ₋2 λ _ _ → isProp→ (isProp→isSet pB _ _)
  isProp-g-cong : isProp (∀ {x y} → x ≡ y → g₁ x ≡ g₁ y)
  isProp-g-cong = isPropΠ₋2 λ _ _ → isProp→ (isProp→isSet pA _ _)

Iff→←ⓢ : isProp A → isProp B → (H : A ⇔ B) → Iff→ⓢ (Iff←ⓢ H) ≡ H
Iff→←ⓢ pA pB _ = isProp⇔ pA pB _ _

Iff←→ⓢ : isProp A → isProp B → (H : A ↔ B) → Iff←ⓢ (Iff→ⓢ H) ≡ H
Iff←→ⓢ pA pB _ = isProp↔ pA pB _ _

Iff≅ⓢ : isProp A → isProp B → (A ↔ B) ≅ (A ⇔ B)
Iff≅ⓢ pA pB = mk≅ Iff→ⓢ Iff←ⓢ (Iff→←ⓢ pA pB) (Iff←→ⓢ pA pB)

Iff≡ⓢ : isProp A → isProp B → (A ↔ B) ≡ (A ⇔ B)
Iff≡ⓢ pA pB = ua $ Iff≅ⓢ pA pB

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
        (ProdEq (isProp-r r _) (isProp-l l _)) refl
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
