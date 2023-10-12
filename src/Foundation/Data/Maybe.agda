module Foundation.Data.Maybe where

open import Foundation.Prelude
open import Foundation.Data.Sum
open import Foundation.Data.Unit
open import Foundation.Relation.Nullary.Discrete

open import Data.Maybe public
  using ()
  renaming (Maybe to infix 30 _？; nothing to none; just to some)

open import Data.Maybe.Properties public
  using ()
  renaming (just-injective to some-inj)

open import Cubical.Data.Maybe
  using (Maybe≡SumUnit)
  renaming (
    Maybe to infix 30 _？🧊; nothing to none🧊; just to some🧊;
    discreteMaybe to discreteMaybe🧊
  )

open import Cubical.Data.Sum
  using ()
  renaming (_⊎_ to infixr 5 _⊎🧊_)

Maybe→🧊 : A ？ → A ？🧊
Maybe→🧊 none = none🧊
Maybe→🧊 (some x) = some🧊 x

Maybe←🧊 : A ？🧊 → A ？
Maybe←🧊 none🧊 = none
Maybe←🧊 (some🧊 x) = some x

Maybe→←🧊 : (x : A ？🧊) → Maybe→🧊 (Maybe←🧊 x) ＝ x
Maybe→←🧊 none🧊 = refl
Maybe→←🧊 (some🧊 x) = refl

Maybe←→🧊 : (x : A ？) → Maybe←🧊 (Maybe→🧊 x) ＝ x
Maybe←→🧊 none = refl
Maybe←→🧊 (some x) = refl

Maybe≅🧊 : A ？ ≅ A ？🧊
Maybe≅🧊 = mk≅ Maybe→🧊 Maybe←🧊 Maybe→←🧊 Maybe←→🧊

Maybe＝🧊 : A ？ ＝ A ？🧊
Maybe＝🧊 = ua Maybe≅🧊

discreteMaybe : discrete A → discrete (A ？)
discreteMaybe disA = subst discrete Maybe＝🧊 $
  discrete←🧊 $ discreteMaybe🧊 $ discrete→🧊 disA

Maybe＝SumUnit : A ？ ＝ ⊤ ⊎ A
Maybe＝SumUnit {A} =
  A ？ ＝⟨ Maybe＝🧊 ⟩
  A ？🧊 ＝⟨ Eq←🧊 Maybe≡SumUnit ⟩
  ⊤ ⊎🧊 A ＝˘⟨ Sum＝🧊 ⟩
  ⊤ ⊎ A ∎

isSetMaybe : isSet A → isSet (A ？)
isSetMaybe setA = subst isSet Maybe＝SumUnit (isSet⊎ isSet⊤ setA)
