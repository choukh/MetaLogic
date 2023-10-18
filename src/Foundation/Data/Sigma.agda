module Foundation.Data.Sigma where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete

open import Data.Product public
  using ()
  renaming (_×_ to infixr 6 _×_)

open import Data.Product.Properties public
  using ()
  renaming (≡-dec to discreteΣ)

open import Cubical.Data.Sigma
  using (Σ≡Prop)

SigEq₁ : isPred P → {u v : Σ A P}
       → (p : u .fst ＝ v .fst) → u ＝ v
SigEq₁ pP H = Eq←🧊 $ Σ≡Prop (isPred→🧊 pP) (Eq→🧊 H)

ProdEq : {x y : A × B} → fst x ＝ fst y → snd x ＝ snd y → x ＝ y
ProdEq refl refl = refl

discrete× : discrete A → discrete B → discrete (A × B)
discrete× dA dB = discreteΣ dA dB
