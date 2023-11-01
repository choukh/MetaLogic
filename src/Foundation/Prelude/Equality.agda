module Foundation.Prelude.Equality where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function

open import Relation.Binary.PropositionalEquality public
  using (sym; cong)

open import Cubical.Data.Equality public
  using (
    funExt;
    _≃_
  )
  renaming (
    happly        to funExt⁻;
    eqToPath      to Eq→🧊;
    pathToEq      to Eq←🧊;
    Path≡Eq       to Eq≡˘🧊;
    Iso           to infix 4 _≅_;
    iso           to mk≅;
    isoToIsoPath  to Iso→🧊;
    isoToEquiv    to Iso→Equiv;
    ua            to ua≃
  )

open _≅_ public

open import Cubical.Foundations.Isomorphism public
  using ()
  renaming (Iso to _≅🧊_)

open import Cubical.Foundations.Equiv public
  using ()
  renaming (_≃_ to _≃🧊_)

infixr 30 _∙_
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

infixr 2 step-≡ step-≡˘
step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
step-≡ _ p q = q ∙ p

step-≡˘ : (x : A) {y z : A} → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ p q = sym q ∙ p

syntax step-≡ x y p = x ≡⟨ p ⟩ y
syntax step-≡˘ x y p = x ≡˘⟨ p ⟩ y

infix 3 _∎
_∎ : (x : A) → x ≡ x
_ ∎ = refl

cong2 : ∀ (f : A → B → C) {x y z w} → x ≡ y → z ≡ w → f x z ≡ f y w
cong2 f refl refl = refl

subst : (P : A → 𝕋 ℓ) {x y : A} → y ≡ x → P x → P y
subst _ refl H = H

subst2 : {x y : A} {z w : B} (R : A → B → 𝕋 ℓ) →
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

EqΠ : (∀ x → P x ≡ Q x) → (∀ x → P x) ≡ (∀ x → Q x)
EqΠ H with funExt H
... | refl = refl

EqΠ2 : (∀ x y → R x y ≡ S x y) → (∀ x y → R x y) ≡ (∀ x y → S x y)
EqΠ2 H = EqΠ λ x → EqΠ λ y → H x y

Eq≡🧊 : {x y : A} → (x ≡ y) ≡ (x ≡🧊 y)
Eq≡🧊 = sym Eq≡˘🧊

Iso←🧊 : A ≅🧊 B → A ≅ B
Iso←🧊 i = mk≅ (fun i) (inv i) (Eq←🧊 ∘ rightInv i) (Eq←🧊 ∘ leftInv i)
  where open _≅🧊_

ua : A ≅ B → A ≡ B
ua = ua≃ ∘ Iso→Equiv
 