module Foundation.Function.SubSpaces where

open import Foundation.Prelude
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Prop.Universe
open import Foundation.Data.Sigma

open import Cubical.Functions.Surjection public
  using ()
  renaming (isSurjection to surjective)

open import Cubical.Functions.Surjection
  using (isEmbedding×isSurjection→isEquiv)

open import Cubical.Functions.Embedding
  using (isEmbedding; injEmbedding)

open import Cubical.Foundations.Equiv
  using (isEquiv; equivToIso)

open import Function as ⓢ
  using (_⇔_; mk⇔)

open ⓢ.Equivalence

injective : (A → B) → 𝕋 _
injective f = ∀ {x y} → f x ≡ f y → x ≡ y

bijective : (A → B) → 𝕋 _
bijective f = injective f × surjective f

isPropInjective : {f : A → B} → isSet A → isProp (injective f)
isPropInjective sA = isPropΠ₋2 λ _ _ → isProp→ (sA _ _)

isPropSurjective : {f : A → B} → isProp (surjective f)
isPropSurjective = isPropΠ λ _ → is1

isPropBijective : {f : A → B} → isSet A → isProp (bijective f)
isPropBijective sA = isProp× (isPropInjective sA) isPropSurjective

_↣_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ↣ B = Σ (A → B) injective

_↠_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ↠ B = Σ (A → B) surjective

_⤖_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ⤖ B = Σ (A → B) bijective

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

⤖→≅ : isSet B → A ⤖ B → A ≅ B
⤖→≅ sB (f , inj , surj) = Iso←🧊 $ equivToIso (f , equiv) where
  equiv : isEquiv f
  equiv = isEmbedding×isSurjection→isEquiv (emb , surj) where
    emb : isEmbedding f
    emb = injEmbedding (isSet→🧊 sB) (Eq→🧊 ∘ inj ∘ Eq←🧊)
