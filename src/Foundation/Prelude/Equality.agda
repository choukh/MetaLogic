module Foundation.Prelude.Equality where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function

open import Cubical.Data.Equality public
  using (
    sym; funExt
  )
  renaming (
    ap to cong;
    eqToPath to ＝→⥱;
    pathToEq to ⥱→＝;
    Path≡Eq to ⥱＝＝;
    Iso to _≅_;
    iso to mk≅
  )

open import Cubical.Data.Equality
  using (isoToEquiv)
  renaming (ua to ua🧊)

subst : (P : A → 𝕋 ℓ) {x y : A} → y ＝ x → P x → P y
subst _ refl H = H

ua : A ≅ B → A ＝ B
ua = ua🧊 ∘ isoToEquiv
