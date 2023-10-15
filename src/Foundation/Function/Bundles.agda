module Foundation.Function.Bundles where

open import Foundation.Prelude.Builtin
open import Foundation.Prelude.Equality
open import Foundation.Logic.Iff

open import Function public
  using (_↣_; _↠_)

open import Function as F
  using (
    _⇔_; _↔_;
    Injective; Surjective
  )

injective : (A → B) → 𝕋 _
injective = Injective _＝_ _＝_

surjective : (A → B) → 𝕋 _
surjective = Surjective _＝_ _＝_

mk↣ : (f : A → B) → injective f → A ↣ B
mk↣ f = F.mk↣

mk↠ : (f : A → B) → surjective f → A ↠ B
mk↠ f = F.mk↠
