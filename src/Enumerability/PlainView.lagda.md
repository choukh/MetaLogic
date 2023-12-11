---
url: foundation.enumerability.plainview
---

# 可枚举性 ▸ 普通视角

```agda
module Enumerability.PlainView where
import Enumerability.ListView.Base as Ⓛ

open import Foundation.Essential
open import Foundation.Data.Maybe
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.List.Discrete

record Enum (A : 𝕋 ℓ) ⦃ discrA : discrete A ⦄ : 𝕋 (ℓ ⁺) where
  field
    ⦃ enumⓁ ⦄ : Ⓛ.Enum A
    Hₗ : ∀ n → length (Ⓛ.enum n) > n

  enum : ℕ → A
  enum n = Σ[<length]? (Ⓛ.enum n) (Hₗ n) .fst

  enum-correct : ∀ n → Ⓛ.enum n [ n ]? ≡ some (enum n)
  enum-correct n = Σ[<length]? (Ⓛ.enum n) (Hₗ n) .snd

  wit : ∀ x → ∃ n ， enum n ≡ x
  wit x = 𝟙.map H (Ⓛ.wit x) where
    H : Ⓛ.Witness Ⓛ.enum x → Σ n ， enum n ≡ x
    H (m , Hm) with ∈→Σ[]⁻¹? Hm
    ... | n , Hn = n , {! enum-correct n !}
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Enumerability/PlainView.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Enumerability.PlainView.html) | [语雀](https://www.yuque.com/ocau/metalogic/enumerability.plainview)  
> 交流Q群: 893531731
