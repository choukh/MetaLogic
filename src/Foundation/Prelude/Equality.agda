module Foundation.Prelude.Equality where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function

open import Cubical.Data.Equality public
  using (
    sym; funExt
  )
  renaming (
    transport to subst;
    eqToPath to ＝→⥱;
    pathToEq to ＝←⥱;
    Iso to _≅_;
    iso to mk≅
  )

open import Cubical.Data.Equality
  using (isoToEquiv)
  renaming (ua to ua🧊)

ua : A ≅ B → A ＝ B
ua = ua🧊 ∘ isoToEquiv
