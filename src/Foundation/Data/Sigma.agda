module Foundation.Data.Sigma where

open import Foundation.Prelude

open import Data.Product public
  using ()
  renaming (_×_ to infixr 6 _×_)

open import Cubical.Data.Sigma
  using (Σ≡Prop)

Σ＝Prop : isPred P → {u v : Σ A P}
       → (p : u .fst ＝ v .fst) → u ＝ v
Σ＝Prop pP H = Eq←🧊 $ Σ≡Prop (isPred→🧊 pP) (Eq→🧊 H)
