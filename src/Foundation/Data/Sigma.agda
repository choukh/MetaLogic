module Foundation.Data.Sigma where

open import Foundation.Prelude

open import Data.Product public
  using ()
  renaming (_×_ to infixr 6 _×_)

open import Cubical.Data.Sigma
  using (Σ≡Prop)

SigEq₁ : isPred P → {u v : Σ A P}
       → (p : u .fst ＝ v .fst) → u ＝ v
SigEq₁ pP H = Eq←🧊 $ Σ≡Prop (isPred→🧊 pP) (Eq→🧊 H)

ProdEq : {x y : A × B} → fst x ＝ fst y → snd x ＝ snd y → x ＝ y
ProdEq refl refl = refl
