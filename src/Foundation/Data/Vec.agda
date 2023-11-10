module Foundation.Data.Vec where

open import Foundation.Prelude

open import Data.Vec public
  using ([]; _∷_)
  renaming (Vec to 𝕍; map to map⃗)

open import Data.Vec.Properties public
  using (map-cong; map-∘)

open import Cubical.Data.Vec as 𝕍
  using ([]; _∷_)
  renaming (Vec to 𝕍🧊)
open 𝕍.VecPath using (isOfHLevelVec)

private variable
  n : ℕ

Vec→🧊 : 𝕍 A n → 𝕍🧊 A n
Vec→🧊 [] = []
Vec→🧊 (x ∷ x⃗) = x ∷ Vec→🧊 x⃗

Vec←🧊 : 𝕍🧊 A n → 𝕍 A n
Vec←🧊 [] = []
Vec←🧊 (x ∷ x⃗) = x ∷ Vec←🧊 x⃗

Vec→←🧊 : (x⃗ : 𝕍🧊 A n) → Vec→🧊 (Vec←🧊 x⃗) ≡ x⃗
Vec→←🧊 [] = refl
Vec→←🧊 (x ∷ x⃗) = cong (x ∷_) (Vec→←🧊 x⃗)

Vec←→🧊 : (x⃗ : 𝕍 A n) → Vec←🧊 (Vec→🧊 x⃗) ≡ x⃗
Vec←→🧊 [] = refl
Vec←→🧊 (x ∷ x⃗) = cong (x ∷_) (Vec←→🧊 x⃗)

Vec≅🧊 : 𝕍 A n ≅ 𝕍🧊 A n
Vec≅🧊 = mk≅ Vec→🧊 Vec←🧊 Vec→←🧊 Vec←→🧊

Vec≡🧊 : 𝕍 A n ≡ 𝕍🧊 A n
Vec≡🧊 = ua Vec≅🧊

isSet𝕍 : isSet A → isSet (𝕍 A n)
isSet𝕍 {n} sA = subst isSet Vec≡🧊 $ mapIsSet (isOfHLevelVec 0 n) sA
