module Foundation.Data.Sigma where

open import Foundation.Prelude

open import Data.Product public
  using (_×_)

open import Cubical.Data.Sigma
  using (Σ≡Prop)

Σ＝Prop : isPred P → {u v : Σ A P}
       → (p : u .fst ＝ v .fst) → u ＝ v
Σ＝Prop pP H = ⥱→＝ $ Σ≡Prop (isPred→🧊 pP) (＝→⥱ H)
