module Foundation.Prelude.Equality where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Function

open import Cubical.Data.Equality public
  using (
    sym; funExt
  )
  renaming (
    ap to cong;
    eqToPath to Eq→🧊;
    pathToEq to Eq←🧊;
    Iso to infix 4 _≅_;
    iso to mk≅
  )

open import Cubical.Data.Equality
  using (isoToEquiv; Path≡Eq)
  renaming (ua to ua🧊)

infixr 30 _∙_
_∙_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q

infixr 2 step-＝ step-＝˘
step-＝ : (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
step-＝ _ p q = q ∙ p

step-＝˘ : (x : A) {y z : A} → y ＝ z → y ＝ x → x ＝ z
step-＝˘ _ p q = sym q ∙ p

syntax step-＝ x y p = x ＝⟨ p ⟩ y
syntax step-＝˘ x y p = x ＝˘⟨ p ⟩ y

infix 3 _∎
_∎ : (x : A) → x ＝ x
_ ∎ = refl

subst : (P : A → 𝕋 ℓ) {x y : A} → y ＝ x → P x → P y
subst _ refl H = H

Eq＝🧊 : {x y : A} → (x ＝ y) ＝ (x ＝🧊 y)
Eq＝🧊 = sym Path≡Eq

ua : A ≅ B → A ＝ B
ua = ua🧊 ∘ isoToEquiv
