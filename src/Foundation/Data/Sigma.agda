module Foundation.Data.Sigma where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete

open import Data.Product public
  using (curry; uncurry)
  renaming (_×_ to infixr 3 _×_)

open import Data.Product.Properties public
  using ()
  renaming (≡-dec to discreteΣ)

open import Cubical.Data.Sigma
  using (Σ≡Prop)

Σ≡p : isPred P → {u v : Σ A P}
       → (p : u .fst ≡ v .fst) → u ≡ v
Σ≡p pP H = Eq←🧊 $ Σ≡Prop (isPred→🧊 pP) (Eq→🧊 H)

×≡ : {x y : A × B} → fst x ≡ fst y → snd x ≡ snd y → x ≡ y
×≡ refl refl = refl

discrete× : discrete A → discrete B → discrete (A × B)
discrete× dA dB = discreteΣ dA dB
