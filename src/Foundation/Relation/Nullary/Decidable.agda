module Foundation.Relation.Nullary.Decidable where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Negation

open import Relation.Nullary public
  using (Dec; yes; no; does)

open import Cubical.Relation.Nullary
  using ()
  renaming (
    Dec to Dec🧊; yes to yes🧊; no to no🧊;
    isPropDec to isPropDec🧊
  )

private variable
  P : A → 𝒰 ℓ

Dec→🧊 : Dec A → Dec🧊 A
Dec→🧊 (yes x) = yes🧊 x
Dec→🧊 (no ¬x) = no🧊 $ ¬→🧊 ¬x

Dec←🧊 : Dec🧊 A → Dec A
Dec←🧊 (yes🧊 x) = yes x
Dec←🧊 (no🧊 ¬x) = no $ ¬←🧊 ¬x

Dec→←🧊 : (H : Dec🧊 A) → Dec→🧊 (Dec←🧊 H) ＝ H
Dec→←🧊 (yes🧊 p) = refl
Dec→←🧊 (no🧊 ¬p) = subst (λ x → no🧊 x ＝ no🧊 ¬p) (sym $ ¬→←🧊 _) refl

Dec←→🧊 : (H : Dec A) → Dec←🧊 (Dec→🧊 H) ＝ H
Dec←→🧊 (yes p) = refl
Dec←→🧊 (no ¬p) = subst (λ x → no x ＝ no ¬p) (sym $ ¬←→🧊 _) refl

Dec≅🧊 : Dec A ≅ Dec🧊 A
Dec≅🧊 = mk≅ Dec→🧊 Dec←🧊 Dec→←🧊 Dec←→🧊

Dec＝🧊 : Dec A ＝ Dec🧊 A
Dec＝🧊 = ua Dec≅🧊

isPropDec : isProp A → isProp (Dec A)
isPropDec H = subst isProp (sym Dec＝🧊) (mapIsProp isPropDec🧊 H)

decidable : (A → 𝒰 ℓ) → 𝒰 _
decidable P = ∀ x → Dec (P x)

deciderOf : {P : A → 𝒰 ℓ} → decidable P → A → 𝔹
deciderOf H x = does $ H x

isPropDecidable : isPred P → isProp (decidable P)
isPropDecidable H = isPropΠ λ x → isPropDec (H x)
