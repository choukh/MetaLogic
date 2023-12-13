module Foundation.Data.Sigma where

open import Foundation.Prelude

open import Data.Product public
  using (curry; uncurry)
  renaming (_×_ to infixr 3 _×_)

open import Data.Product.Properties
  using (,-injectiveʳ-UIP)

open import Cubical.Data.Sigma
  using (Σ≡Prop; Σ-cong-snd)

-- for all hlevel

×≡ : {x y : A × B} → fst x ≡ fst y → snd x ≡ snd y → x ≡ y
×≡ refl refl = refl

Σcong₂ : ((x : A) → P x ≡ Q x) → Σ A P ≡ Σ A Q
Σcong₂ eq = Eq←🧊 $ Σ-cong-snd $ Eq→🧊 ∘ eq

-- for prop

Σ≡p : isPred P → {u v : Σ A P}
       → (p : u .fst ≡ v .fst) → u ≡ v
Σ≡p pP H = Eq←🧊 $ Σ≡Prop (isPred→🧊 pP) (Eq→🧊 H)

isProp× : isProp A → isProp B → isProp (A × B)
isProp× pA pB = isPropΣ pA (λ _ → pB)

-- for set

,-injʳ : ∀ {a} {b c : P a} → isSet A → (Σ A P ∋ (a , b)) ≡ (a , c) → b ≡ c
,-injʳ sA = ,-injectiveʳ-UIP (sA _ _)
