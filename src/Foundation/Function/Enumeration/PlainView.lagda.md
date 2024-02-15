---
url: foundation.enumeration.plainview
---

# 元语言 ▸ 可枚举性 ▸ 普通视角

前篇介绍了可枚举性的累积列表视角. 由于其累积的形式, 虽然方便构造, 但是不方便使用. 本篇介绍可枚举性的第3种视角, 叫做普通视角, 它方便直接使用. 为了防止命名冲突, 本章把累积列表视角的相关概念都加上 `Ⓛ.` 前缀.

```agda
module Foundation.Function.Enumeration.PlainView where
open import Foundation.Function.Enumeration.ListView.Base as Ⓛ
  using (𝕃ₙ; cum-total)

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Truncation

open import Foundation.Data.Maybe
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Sum
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic

open import Foundation.Relation.Nullary.Discrete.Base
open import Foundation.Relation.Nullary.Discrete.List
```

为了得到普通视角, 还需要追加两个条件.

1. 枚举的类型必须是离散的.
2. 累积列表的长度必须是严格递增的, 也叫真累积. 当然, 这样的话, 有限类型将不会有普通视角. 不过我们关心的都是可数无穷类型, 所以这个条件是可以满足的.

```agda
proper : 𝕃ₙ A → 𝕋 _
proper f = ∀ n → length (f n) > n
```

现在, 给定离散集 `A` 和它枚举, 其中的累积列表是真累积.

```agda
module PlainEnum ⦃ _ : discrete A ⦄ ⦃ _ : Ⓛ.Enum A ⦄ (l>_ : proper Ⓛ.enum) where
```

**<u>定义</u>** 由于 `Ⓛ.enum n` 的长度大于 `n`, 它必然在索引 `n` 处有值, 我们就取这个值, 作为 `A` 的普通视角枚举函数 `enum : ℕ → A` 在 `n` 处的值.

```agda
  enum : ℕ → A
  enum n = Ⓛ.enum n [ l> n ]⁻¹!
```

**<u>引理</u>** `enum n` 的值必然等于列表 `Ⓛ.enum n` 中的某个元素.  
**<u>证明</u>** 由 `enum` 的定义即得. ∎

```agda
  cum : ∀ {n} → enum n ∈ Ⓛ.enum n
  cum {n} = []?→∈ _ $ Ⓛ.enum n [ l> n ]⁻¹!≡
```

**<u>引理</u>** `enum` 见证了每一个 `x : A`.  
**<u>证明</u>** 我们有 `x` 在 `Ⓛ.enum` 中的见证 `m`, 需要将它转化成 `x` 在 `enum` 中的见证.

一方面, 由 `x ∈ Ⓛ.enum m`, 可以找到 `n` 满足 `Ⓛ.enum m [ x ]⁻¹? ≡ some n`, 也即 `Ⓛ.enum m [ n ]? ≡ some x`.

另一方面, 由 `enum` 的定义有 `Ⓛ.enum n [ n ]? ≡ some (enum n)`.

由累积列表的性质, 有以下两种情况:

- 若 `Ⓛ.enum n ≡ Ⓛ.enum m ++ xs`, 那么
  `some (enum n) ≡ Ⓛ.enum n [ n ]? ≡ (Ⓛ.enum m ++ xs) [ n ]? ≡ some x`.
- 若 `Ⓛ.enum m ≡ Ⓛ.enum n ++ xs`, 那么
  `some (enum n) ≡ (Ⓛ.enum n ++ xs) [ n ]? ≡ Ⓛ.enum m [ n ]? ≡ some x`.

不管怎样, 都有 `some (enum n) ≡ some x`. 由 `some` 的单射性即得 `enum n ≡ x`. ∎

```agda
  wit : ∀ x → ∃ n ， enum n ≡ x
  wit x = 𝟙.map H (Ⓛ.wit x) where
    H : Ⓛ.Witness Ⓛ.enum x → Σ n ， enum n ≡ x
    H (m , Hm) with some[]⁻¹-intro Hm
    H (m , Hm) | n , Hn with cum-total Ⓛ.cum m n
      | Ⓛ.enum n [ l> n ]⁻¹!≡   -- = H1 : Ⓛ.enum n [ n ]? ≡ some (enum n)
      | some[]⁻¹→some[] (Ⓛ.enum m) Hn   -- = H2 : Ⓛ.enum m [ n ]? ≡ some x
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
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/PlainView.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Function.Enumeration.PlainView.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.enumeration.plainview)  
> 交流Q群: 893531731
 