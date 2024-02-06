module Foundation.Data.Sum where

open import Foundation.Prelude
open import Foundation.Data.Empty

open import Data.Sum public
  using (inj₁; inj₂; map₁; map₂)
  renaming (_⊎_ to infixr 4.1 _⊎_)

open import Cubical.Data.Sum as 🧊
  using (inl; inr)

Sum→🧊 : A ⊎ B → A 🧊.⊎ B
Sum→🧊 (inj₁ x) = inl x
Sum→🧊 (inj₂ y) = inr y

Sum←🧊 : A 🧊.⊎ B → A ⊎ B
Sum←🧊 (inl x) = inj₁ x
Sum←🧊 (inr y) = inj₂ y

Sum→←🧊 : (x : A 🧊.⊎ B) → Sum→🧊 (Sum←🧊 x) ≡ x
Sum→←🧊 (inl x) = refl
Sum→←🧊 (inr x) = refl

Sum←→🧊 : (x : A ⊎ B) → Sum←🧊 (Sum→🧊 x) ≡ x
Sum←→🧊 (inj₁ x) = refl
Sum←→🧊 (inj₂ y) = refl

Sum≅🧊 : A ⊎ B ≅ A 🧊.⊎ B
Sum≅🧊 = mk≅ Sum→🧊 Sum←🧊 Sum→←🧊 Sum←→🧊

Sum≡🧊 : A ⊎ B ≡ A 🧊.⊎ B
Sum≡🧊 = ua Sum≅🧊

isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ pA pB disj = subst isProp Sum≡🧊 $
  isProp←🧊 $ 🧊.isProp⊎ (isProp→🧊 pA) (isProp→🧊 pB) λ x y → Empty→🧊 (disj x y)

isSet⊎ : isSet A → isSet B → isSet (A ⊎ B)
isSet⊎ sA sB = subst isSet Sum≡🧊 $
  isSet←🧊 $ 🧊.isSet⊎ (isSet→🧊 sA) (isSet→🧊 sB)
