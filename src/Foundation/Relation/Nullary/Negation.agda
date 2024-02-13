module Foundation.Relation.Nullary.Negation where

open import Foundation.Prelude
open import Foundation.Data.Empty
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

stable : 𝕋 ℓ → 𝕋 ℓ
stable A = nonEmpty A → A
