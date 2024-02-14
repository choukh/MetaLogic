module Foundation.Relation.Nullary.Negation where

open import Foundation.Prelude
open import Foundation.Data.Empty
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation

open import Relation.Nullary public
  using ()
  renaming (¬_ to infix 30 ¬_)

import Cubical.Relation.Nullary as 🧊

¬→🧊 : ¬ A → 🧊.¬ A
¬→🧊 ¬x x with ¬x x
...| ()

¬←🧊 : 🧊.¬ A → ¬ A
¬←🧊 ¬x x with ¬x x
...| ()

¬→←🧊 : (¬x : 🧊.¬ A) → ¬→🧊 (¬←🧊 ¬x) ≡ ¬x
¬→←🧊 ¬x = funExt λ x → exfalso $ ¬←🧊 ¬x x

¬←→🧊 : (¬x : ¬ A) → ¬←🧊 (¬→🧊 ¬x) ≡ ¬x
¬←→🧊 ¬x = funExt λ x → exfalso $ ¬x x

¬≅🧊 : ¬ A ≅ (🧊.¬ A)
¬≅🧊 = mk≅ ¬→🧊 ¬←🧊 ¬→←🧊 ¬←→🧊

¬≡🧊 : ¬ A ≡ (🧊.¬ A)
¬≡🧊 = ua ¬≅🧊

nonEmpty : 𝕋 ℓ → 𝕋 ℓ
nonEmpty A = ¬ ¬ A

nonEmptyTrunc : nonEmpty A ↔ nonEmpty ∥ A ∥₁
nonEmptyTrunc .⇒ ¬¬a ¬∣a∣ = ¬¬a λ a → ¬∣a∣ ∣ a ∣₁
nonEmptyTrunc .⇐ ¬¬∣a∣ = ¬¬∣a∣ ∘ 𝟙.rec isProp⊥

stable : 𝕋 ℓ → 𝕋 ℓ
stable A = nonEmpty A → A

stable₁ : 𝕋 ℓ → 𝕋 ℓ
stable₁ A = nonEmpty A → ∥ A ∥₁

stable-subst : A ↔ B → stable A → stable B
stable-subst iff stbA ¬¬b = iff .⇒ $ stbA λ ¬a → ¬¬b λ b → ¬a $ iff .⇐ b

stableTrunc : stable₁ A → stable ∥ A ∥₁
stableTrunc stbA ne = stbA (nonEmptyTrunc .⇐ ne)
