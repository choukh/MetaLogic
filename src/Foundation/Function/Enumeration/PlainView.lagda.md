---
url: foundation.enumeration.plainview
---

# 元语言 ▸ 可枚举性 ▸ 普通视角

```agda
module Foundation.Function.Enumeration.PlainView where
open import Foundation.Function.Enumeration.ListView.Base as Ⓛ
  using (𝕃ₙ; cum; cum-total)

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Truncation

open import Foundation.Data.Maybe
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Sum
open import Foundation.Data.List

open import Foundation.Relation.Nullary.Discrete.Base
open import Foundation.Relation.Nullary.Discrete.List

proper : 𝕃ₙ A → 𝕋 _
proper f = ∀ n → length (f n) > n

module _ ⦃ _ : discrete A ⦄ ⦃ _ : Ⓛ.Enum A ⦄ (p : proper Ⓛ.enum) where

  enum : ℕ → A
  enum n = Σ[<length]? (Ⓛ.enum n) (p n) .fst

  wit : ∀ x → ∃ n ， enum n ≡ x
  wit x = 𝟙.map H (Ⓛ.wit x) where
    H : Ⓛ.Witness Ⓛ.enum x → Σ n ， enum n ≡ x
    H (m , Hm) with ∈→Σ[]⁻¹? Hm
    H (m , Hm) | n , Hn with cum-total cum m n
      | Σ[<length]? (Ⓛ.enum n) (p n) .snd  -- = H1 : Ⓛ.enum n [ n ]? ≡ some (enum n)
      | index-inv (Ⓛ.enum m) Hn            -- = H2 : Ⓛ.enum m [ n ]? ≡ some x
    ... | inj₁ (xs , n≡m++) | H1 | H2 = n , some-inj (
      some (enum n)           ≡˘⟨ H1 ⟩
      Ⓛ.enum n [ n ]?         ≡⟨ cong _[ n ]? n≡m++ ⟩
      (Ⓛ.enum m ++ xs) [ n ]? ≡⟨ ++[]? (Ⓛ.enum m) H2 ⟩
      some x                  ∎)
    ... | inj₂ (xs , m≡n++) | H1 | H2 = n , some-inj (
      some (enum n)           ≡˘⟨ ++[]? (Ⓛ.enum n) H1 ⟩
      (Ⓛ.enum n ++ xs) [ n ]? ≡˘⟨ cong _[ n ]? m≡n++ ⟩
      Ⓛ.enum m [ n ]?         ≡⟨ H2 ⟩
      some x                  ∎)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/PlainView.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Function.Enumeration.PlainView.html) | [语雀](https://www.yuque.com/ocau/metalogic/enumeration.plainview)  
> 交流Q群: 893531731
