module Foundation.Prelude.Equality where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function

open import Relation.Binary.PropositionalEquality public
  using (_≗_; sym; cong)

open import Cubical.Data.Equality public
  using (
    funExt; _≃_
  )
  renaming (
    happly        to funExt⁻;
    eqToPath      to Eq→🧊;
    pathToEq      to Eq←🧊;
    Iso           to infix 4 _≅_;
    iso           to mk≅;
    isoToIsoPath  to Iso→🧊;
    isoToEquiv    to Iso→Equiv;
    ua            to ua≃
  )

open import Cubical.Data.Equality
  using (eqToPath-pathToEq; pathToEq-eqToPath)

open import Cubical.Foundations.Isomorphism public
  using ()
  renaming (Iso to _≅🧊_)

open import Cubical.Foundations.Equiv public
  using ()
  renaming (_≃_ to _≃🧊_)

open _≅_ public
open _≅🧊_ public

--------------------------------------------------------------------------------
-- Properties

infixr 30 _∙_
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

infixr 2 _≡⟨_⟩_ _≡˘⟨_⟩_
_≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_≡˘⟨_⟩_ : (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
_ ≡˘⟨ p ⟩ q = sym p ∙ q

infix 3 _∎
_∎ : (x : A) → x ≡ x
_ ∎ = refl

cong2 : ∀ (f : A → B → C) {x y z w} → x ≡ y → z ≡ w → f x z ≡ f y w
cong2 f refl refl = refl

subst : (P : A → 𝕋 ℓ) {x y : A} → y ≡ x → P x → P y
subst _ refl H = H

subst2 : (R : A → B → 𝕋 ℓ) {x y : A} {z w : B} →
         x ≡ y → z ≡ w → R x z → R y w
subst2 R refl refl = id

subst3 : {x y : A} {z w : B} {u v : C} (R : A → B → C → 𝕋 ℓ) →
         x ≡ y → z ≡ w → u ≡ v → R x z u → R y w v
subst3 R refl refl refl = id

subst4 : {x y : A} {z w : B} {u v : C} {s t : D} (R : A → B → C → D → 𝕋 ℓ) →
         x ≡ y → z ≡ w → u ≡ v → s ≡ t → R x z u s → R y w v t
subst4 R refl refl refl refl = id

funExt2 : {R : A → B → 𝕋 ℓ} {f g : (x : A) (y : B) → R x y} →
          ((x : A) (y : B) → f x y ≡ g x y) → f ≡ g
funExt2 H = funExt λ x → funExt λ y → H x y

ua : A ≅ B → A ≡ B
ua = ua≃ ∘ Iso→Equiv

EqΠ : (∀ x → P x ≡ Q x) → (∀ x → P x) ≡ (∀ x → Q x)
EqΠ H with funExt H
... | refl = refl

EqΠ2 : (∀ x y → R₁ x y ≡ R₂ x y) → (∀ x y → R₁ x y) ≡ (∀ x y → R₂ x y)
EqΠ2 H = EqΠ λ x → EqΠ λ y → H x y

--------------------------------------------------------------------------------
-- 🧊 Conversion

Eq→←🧊 : {x y : A} (p : x ≡🧊 y) → Eq→🧊 (Eq←🧊 p) ≡ p
Eq→←🧊 = Eq←🧊 ∘ eqToPath-pathToEq

Eq←→🧊 : {x y : A} (p : x ≡ y) → Eq←🧊 (Eq→🧊 p) ≡ p
Eq←→🧊 = Eq←🧊 ∘ pathToEq-eqToPath

Eq≅🧊 : {x y : A} → (x ≡ y) ≅ (x ≡🧊 y)
Eq≅🧊 = mk≅ Eq→🧊 Eq←🧊 Eq→←🧊 Eq←→🧊

Eq≡🧊 : {x y : A} → (x ≡ y) ≡ (x ≡🧊 y)
Eq≡🧊 = ua Eq≅🧊

Iso←🧊 : A ≅🧊 B → A ≅ B
Iso←🧊 i = mk≅ (fun i) (inv i) (Eq←🧊 ∘ rightInv i) (Eq←🧊 ∘ leftInv i)
  where open _≅🧊_

Iso≅🧊 : (A ≅ B) ≅ (A ≅🧊 B)
Iso≅🧊 = mk≅ Iso→🧊 Iso←🧊 (Eq←🧊 ∘ right) left where
  right : ∀ iso → Iso→🧊 (Iso←🧊 iso) ≡🧊 iso
  fun (right iso i) = iso .fun
  inv (right iso i) = iso .inv
  rightInv (right iso i) y = eqToPath-pathToEq (iso .rightInv y) i
  leftInv (right iso i) y = eqToPath-pathToEq (iso .leftInv y) i
  left : ∀ iso → Iso←🧊 (Iso→🧊 iso) ≡ iso
  left (mk≅ fun inv rightInv leftInv) = cong2 (mk≅ fun inv)
    (funExt $ Eq←→🧊 ∘ rightInv)
    (funExt $ Eq←→🧊 ∘ leftInv)

Iso≡🧊 : (A ≅ B) ≡ (A ≅🧊 B)
Iso≡🧊 = ua Iso≅🧊
