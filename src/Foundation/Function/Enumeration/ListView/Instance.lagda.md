---
url: foundation.enumeration.listview.instance
---

# 元语言 ▸ 可枚举性 ▸ 累积列表视角 ▸ 实例

本章给出一些基本类型的枚举. 我们从 `Foundation` 和标准库中导入了相关定义和引理.

```agda
{-# OPTIONS --lossy-unification #-}
module Foundation.Function.Enumeration.ListView.Instance where
open import Foundation.Function.Enumeration.ListView.Base

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Truncation

open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Sigma
open import Foundation.Data.Sum
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic
open import Foundation.Data.Vec
```

**<u>约定</u>** 本章使用 `m` `n` `o` 表示自然数.

```agda
private variable
  m n o : ℕ
```

**<u>实例/构造</u>** 布尔值枚举: 取常序列 `λ _ → true ∷ [ false ]` 即可. 这样每项都比前项多了空后段, 且显然所有布尔值都被见证了. ∎

```agda
instance
  enum𝔹 : Enum 𝔹
  enum𝔹 = mkEnum (λ _ → true ∷ [ false ]) (λ n → [] , refl)
    λ { true →  ex 0 $ here refl
      ; false → ex 0 $ there (here refl) }
```

**<u>实例/构造</u>** 自然数枚举: 序列的第 `0` 项取 `[ 0 ]`, 第 `suc n` 项取 `e n ++ [ suc n ]` 即可. 这样每项都比前项多了后段 `[ suc n ]`, 且显然所有自然数都被见证了. ∎

```agda
  enumℕ : Enum ℕ
  enumℕ = mkEnum e c w where
    e : 𝕃ₙ ℕ
    e zero = [ 0 ]
    e (suc n) = e n ++ [ suc n ]
    c : Cumulation e
    c _ = _ , refl
    w : ∀ n → e witness n
    w n = ex n (H n) where
      H : ∀ n → n ∈ e n
      H zero = here refl
      H (suc n) = ∈++-introʳ (here refl)
```

**<u>实例/构造</u>** 可枚举集的笛卡尔积可枚举: 取两集合枚举的每项的笛卡尔积, 累积起来即可. `(x , y)` 的见证是 `x` 的见证加 `y` 的见证. ∎

```agda
  enum× : ⦃ Enum A ⦄ → ⦃ Enum B ⦄ → Enum (A × B)
  enum× {A} {B} = mkEnum e c w where
    e : 𝕃ₙ (A × B)
    e zero = enum 0 [×] enum 0
    e (suc n) = e n ++ enum n [×] enum n
    c : Cumulation e
    c n = enum n [×] enum n , refl
    w : ∀ xy → e witness xy
    w (x , y) = 𝟙.map2 H (wit x) (wit y) where
      H : Witness enum x → Witness enum y → Witness e (x , y)
      H (m , x∈fm) (n , x∈gn) = suc (m + n) , ∈++-introʳ H2 where
        H2 : (x , y) ∈ enum (m + n) [×] enum (m + n)
        H2 = ∈[×]-intro (cum-≤→⊆ cum m≤m+n x∈fm) (cum-≤→⊆ cum m≤n+m x∈gn)
```

**<u>实例/构造</u>** 可枚举集的 `n` 维向量可枚举: 第 `0` 项取空列表, 第 `suc m` 项取前一项并上 `enum m` 的 `n` 维组合. 其中 `enum m` 是可枚举集的累积列表的第 `m` 项. 见证条件的证明留作练习. ∎

```agda
  enum𝕍 : ⦃ Enum A ⦄ → Enum (𝕍 A n)
  enum𝕍 {A} = mkEnum e c w where
    e : 𝕃ₙ (𝕍 A n)
    e zero = []
    e {n} (suc m) = e m ++ combine (enum m) n

    c : Cumulation e
    c _ = _ , refl

    e-≤→⊆ : {x⃗ : 𝕍 A n} → m ≤ o → x⃗ ∈ e m → x⃗ ∈ combine (enum o) n
    e-≤→⊆ {m = suc m} sm≤o H with ∈++-elim (e m) H
    ... | inj₁ x⃗∈en   = e-≤→⊆ (m+n≤o⇒n≤o 1 sm≤o) x⃗∈en
    ... | inj₂ x⃗∈comb = combine-≤→⊆ cum (m+n≤o⇒n≤o 1 sm≤o) x⃗∈comb

    w : (x⃗ : 𝕍 A n) → e witness x⃗
    w [] = ex 1 (here refl)
    w (x ∷ x⃗) = 𝟙.map2 H (wit x) (w x⃗) where
      H : Witness enum x → Witness e x⃗ → Witness e (x ∷ x⃗)
      H (m , Hm) (suc n , Hn) = suc m + suc n , ∈++-introʳ (∈map[×]-intro H1 H2) where
        H1 : x ∈ enum (m + suc n)
        H1 = cum-≤→⊆ cum m≤m+n Hm
        H2 : x⃗ ∈ combine (enum (m + suc n)) _
        H2 = e-≤→⊆ m≤n+m Hn
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/ListView/Instance.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Function.Enumeration.ListView.Instance.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.enumeration.listview.instance)  
> 交流Q群: 893531731
