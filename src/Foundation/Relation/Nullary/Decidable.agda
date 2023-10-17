module Foundation.Relation.Nullary.Decidable where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Negation

open import Relation.Nullary public
  using (Dec; yes; no; does)

open import Cubical.Relation.Nullary as 🧊
  using ()

Dec→🧊 : Dec A → 🧊.Dec A
Dec→🧊 (yes x) = 🧊.yes x
Dec→🧊 (no ¬x) = 🧊.no $ ¬→🧊 ¬x

Dec←🧊 : 🧊.Dec A → Dec A
Dec←🧊 (🧊.yes x) = yes x
Dec←🧊 (🧊.no ¬x) = no $ ¬←🧊 ¬x

Dec→←🧊 : (H : 🧊.Dec A) → Dec→🧊 (Dec←🧊 H) ＝ H
Dec→←🧊 (🧊.yes p) = refl
Dec→←🧊 (🧊.no ¬p) = subst (λ x → 🧊.no x ＝ 🧊.no ¬p) (¬→←🧊 _) refl

Dec←→🧊 : (H : Dec A) → Dec←🧊 (Dec→🧊 H) ＝ H
Dec←→🧊 (yes p) = refl
Dec←→🧊 (no ¬p) = subst (λ x → no x ＝ no ¬p) (¬←→🧊 _) refl

Dec≅🧊 : Dec A ≅ 🧊.Dec A
Dec≅🧊 = mk≅ Dec→🧊 Dec←🧊 Dec→←🧊 Dec←→🧊

Dec＝🧊 : Dec A ＝ 🧊.Dec A
Dec＝🧊 = ua Dec≅🧊

isPropDec : isProp A → isProp (Dec A)
isPropDec H = subst isProp Dec＝🧊 (mapIsProp 🧊.isPropDec H)

Decℙ : (A → 𝕋 ℓ) → 𝕋 _
Decℙ P = ∀ x → Dec (P x)

decider : {P : A → 𝕋 ℓ} → Decℙ P → A → 𝔹
decider H x = does $ H x

isPropDecℙ : isPred P → isProp (Decℙ P)
isPropDecℙ H = isPropΠ λ x → isPropDec (H x)
