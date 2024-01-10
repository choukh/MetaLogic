module Foundation.Relation.Nullary.Decidable where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Negation

open import Relation.Nullary public
  using (Dec; yes; no; does)

import Cubical.Relation.Nullary as 🧊

Dec→🧊 : Dec A → 🧊.Dec A
Dec→🧊 (yes x) = 🧊.yes x
Dec→🧊 (no ¬x) = 🧊.no $ ¬→🧊 ¬x

Dec←🧊 : 🧊.Dec A → Dec A
Dec←🧊 (🧊.yes x) = yes x
Dec←🧊 (🧊.no ¬x) = no $ ¬←🧊 ¬x

Dec→←🧊 : (H : 🧊.Dec A) → Dec→🧊 (Dec←🧊 H) ≡ H
Dec→←🧊 (🧊.yes p) = refl
Dec→←🧊 (🧊.no ¬p) = subst (λ x → 🧊.no x ≡ 🧊.no ¬p) (¬→←🧊 _) refl

Dec←→🧊 : (H : Dec A) → Dec←🧊 (Dec→🧊 H) ≡ H
Dec←→🧊 (yes p) = refl
Dec←→🧊 (no ¬p) = subst (λ x → no x ≡ no ¬p) (¬←→🧊 _) refl

Dec≅🧊 : Dec A ≅ 🧊.Dec A
Dec≅🧊 = mk≅ Dec→🧊 Dec←🧊 Dec→←🧊 Dec←→🧊

Dec≡🧊 : Dec A ≡ 🧊.Dec A
Dec≡🧊 = ua Dec≅🧊

isPredDec : isProp A → isProp (Dec A)
isPredDec H = subst isProp Dec≡🧊 (mapIsProp 🧊.isPropDec H)

Decℙ : (A → 𝕋 ℓ) → 𝕋 _
Decℙ P = ∀ x → Dec (P x)

decider : {P : A → 𝕋 ℓ} → Decℙ P → A → 𝔹
decider H x = does $ H x

isPredDecℙ : isPred P → isProp (Decℙ P)
isPredDecℙ H = isPropΠ λ x → isPredDec (H x)
