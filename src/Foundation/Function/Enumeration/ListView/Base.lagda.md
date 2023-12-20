---
url: foundation.enumeration.listview.base
---

# 元语言 ▸ 可枚举性 ▸ 累积列表视角 ▸ 定义

本章介绍枚举的第2种视角.

```agda
{-# OPTIONS --lossy-unification #-}
module Foundation.Function.Enumeration.ListView.Base where

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Sum
open import Foundation.Data.Sigma
```

我们需要同时谈论列表的 `_∈_` 和向量的 `_∈_`, 分别记作 `_∈ᴸ_` 和 `_∈⃗_`, 以示区别.

```agda
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)
open import Foundation.Data.Vec
open import Foundation.Data.Vec.SetTheoretic
  renaming (_∈_ to _∈⃗_)
```

## 累积列表

**<u>定义</u>** 给定 `A`, 我们把由 `A` 的列表组成的无穷序列记作 `𝕃ₙ A`, 简称 `A` 的列表序列.

```agda
𝕃ₙ : 𝕋 ℓ → 𝕋 ℓ
𝕃ₙ A = ℕ → 𝕃 A
```

**<u>约定</u>** 本章使用 `f` 表示某 `A` 的列表序列, `m` `n` `o` 表示自然数.

```agda
private variable
  f : 𝕃ₙ A
  m n o : ℕ
```

**<u>定义</u>** 列表序列 `f : 𝕃ₙ A` 的一个累积, 记作 `Cumulation f`, 是一个以 `n : ℕ` 为索引的集族, 对每个 `n` 都给出了一个 `xs : 𝕃 A`, 使得 `f (suc n) ≡ f n ++ xs` 成立. 其中 `_++_` 是列表的拼接操作.

```agda
Cumulation : 𝕃ₙ A → 𝕋 _
Cumulation f = ∀ n → Σ xs ， f (suc n) ≡ f n ++ xs
```

给出了累积的列表序列简称累积列表. 现在, 给定一个累积列表, 以下列出它的一些性质. 它们都非常显然, 我们略去自然语言证明.

```agda
module _ (cum : Cumulation f) where
```

**<u>引理</u>** 累积列表的任意两个项有共同的前段, 而排在后面的项 (以下简称后项) 比排在前面的项 (以下简称前项) 多了一个后段 (可能为空).

```agda
  cum-≤→Σ : m ≤ n → Σ xs ， f n ≡ f m ++ xs
  cum-≤→Σ ≤-refl = [] , (sym $ ++-identityʳ _)
  cum-≤→Σ (≤-step {n} m≤n) with cum-≤→Σ m≤n | cum n
  ... | xs , Hx | ys , Hy rewrite Hy | Hx = xs ++ ys , ++-assoc _ _ _
```

**<u>引理</u>** 累积列表的任意两个项中必有一个项比另一个项多一个后段.

```agda
  cum-total : ∀ m n → (Σ xs ， f n ≡ f m ++ xs) ⊎ (Σ xs ， f m ≡ f n ++ xs) 
  cum-total m n with ≤-total m n
  ... | inj₁ m≤n = inj₁ (cum-≤→Σ m≤n)
  ... | inj₂ n≤m = inj₂ (cum-≤→Σ n≤m)
```

**<u>引理</u>** 对累积列表的任意两个项, 前项包含于后项.

```agda
  cum-≤→⊆ : m ≤ n → f m ⊆ f n
  cum-≤→⊆ m≤n x∈fm with cum-≤→Σ m≤n
  ... | xs , eq = subst (_ ∈ᴸ_) eq (∈-++⁺ˡ x∈fm)
```

**<u>引理</u>** 对累积列表的任意两个项, 前项的长度小于等于后项的长度.

```agda
  cum-length : m ≤ n → length (f m) ≤ length (f n)
  cum-length {m} {n} m≤n with cum-≤→Σ m≤n
  ... | xs , eq = subst (_ ≤_) H m≤m+n where
    H = length (f n)              ≡⟨ cong length eq ⟩
        length (f m ++ xs)        ≡⟨ length-++ _ ⟩
        length (f m) + length xs  ∎
```

## 枚举的定义

**<u>定义</u>** `x : A` 在列表序列 `f : 𝕃ₙ A` 中的见证集, 记作 `Witness f x`, 定义为满足 `x ∈ᴸ f n` 的所有 `n` (称为 `x` 的见证) 组成的集合.

```agda
Witness : 𝕃ₙ A → A → 𝕋 _
Witness f x = Σ n ， x ∈ᴸ f n
```

**<u>定义</u>** 我们说 `f` 见证了 `x`, 记作 `f witness x`, 当且仅当见证集 `Witness f x` 有值, 也即存在 `x` 的见证.

```agda
_witness_ : 𝕃ₙ A → A → 𝕋 _
f witness x = ∥ Witness f x ∥₁
```

**<u>定义</u>** `A` 的枚举 `Enum A` 是一个二元组

1. “见证了所有 `x : A`” (该条件记作 `wit`) 的列表序列 `enum : 𝕃ₙ A`
2. `enum` 的一个累积 `cum : Cumulation enum`

```agda
record Enum (A : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  constructor mkEnum
  field
    enum : 𝕃ₙ A
    cum : Cumulation enum
    wit : ∀ x → enum witness x
```

**<u>约定</u>** 对一种类型, 我们只会谈论它的一种枚举. 它在上下文中是明确的, 首次出现时会放在括号 `⦃ ⦄` 中或使用 `instance` 关键字来声明, 所以每次提到枚举中的概念时不会一一带上该枚举作为参数, 从而精简表达. 该约定表达为以下代码.

```agda
open Enum ⦃...⦄ public
```

**<u>定义</u>** 我们说 `A` 递归可枚举, 当且仅当存在 `A` 的一个枚举.

```agda
enumerable : 𝕋 ℓ → 𝕋 _
enumerable A = ∥ Enum A ∥₁
```

与可选值序列视角类似的, 我们有性质的枚举. 当性质为恒真时, 这两种枚举可以相互转化.

```agda
record Enumℙ {A : 𝕋 ℓ} (P : A → 𝕋 ℓ′) : 𝕋 (ℓ ⊔ ℓ′) where
  constructor mkEnumℙ
  field
    enumℙ : 𝕃ₙ A
    cumℙ : Cumulation enumℙ
    witℙ : ∀ x → P x ↔ enumℙ witness x

Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
Enum↔ℙ = ⇒: (λ (mkEnum f cum H) → mkEnumℙ f cum λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
          ⇐: (λ (mkEnumℙ f cum H) → mkEnum f cum λ x → H x .⇒ tt)

enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
enumerableℙ P = ∥ Enumℙ P ∥₁

enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
enumerable↔ℙ = ↔-map Enum↔ℙ
```

**<u>事实</U>** 可选值序列视角与累积列表视角等价.  
**<u>证明</U>** 见代码 [`Enum↔Ⓜ`](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/ListView/Properties.agda#L145). ∎

累积列表视角的定义就到此为止了, 但我们额外介绍一个特殊构造, 用于后篇证明向量的可枚举性.

## 列表元素的组合

**<u>定义</u>** 列表 `xs : 𝕃 A` 的 `n` 维组合是一个由 `A` 的 `n` 维向量组成的列表, 依维数的不同, 递归定义如下

- 当维数为零时, 输出由空向量组成的单元素列表.
- 当维数为 `suc n` 时, 输出所有形如以下的 `suc n` 维向量所组成的列表.
  - 从 `xs` 中取出一个元素 `x` 作为向量的头部, 从 `xs` 的 `n` 维组合中取出一个元素 (`n` 维向量) 作为向量的尾部, 组成 `suc n` 维向量.

```agda
combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (uncurry _∷_) (xs [×] combine xs n)
```

**<u>引理</u>** 对任意累积列表和维数 `n`, 前项的 `n` 维组合包含于后项的 `n` 维组合.  
**<u>证明</u>** 直观上, 由于前项包含于后项, 前项元素的组合也必定包含于后项元素的组合. ∎

```agda
combine-≤→⊆ : Cumulation f → m ≤ o → combine (f m) n ⊆ combine (f o) n
combine-≤→⊆ {n = zero} _ _ H = H
combine-≤→⊆ {n = suc n} cum m≤o H with ∈map[×]-elim H
... | x , y , x∈ , y∈ , refl = ∈map[×]-intro (cum-≤→⊆ cum m≤o x∈) (combine-≤→⊆ cum m≤o y∈)
```

**<u>引理</u>** 对 `A` 的任意累积列表 `f` 和任意 `n` 维向量 `x⃗`, 如果 `f` 见证了 `x⃗` 的所有元素, 那么组合的序列 `λ k → combine (f k) n` 见证了 `x⃗`.  
**<u>证明</u>** 对 `x⃗` 归纳. 若为空向量, 显然被见证. 若为 `x ∷ x⃗`, 取 `x` 的见证 `m` 和 `x⃗` 的见证 `o`, 则 `m + o` 就是 `x ∷ x⃗` 的见证. ∎

```agda
combine-wit : Cumulation f → (x⃗ : 𝕍 A n) →
  (∀ x → x ∈⃗ x⃗ → f witness x) → (λ k → combine (f k) n) witness x⃗
combine-wit _ [] _ = ex 0 (here refl)
combine-wit {f} cum (x ∷ x⃗) wit = 𝟙.map2 H (wit x (here refl)) IH where
    IH = combine-wit cum x⃗ λ y y∈⃗ → wit y (there y∈⃗)
    H : Witness f x → Witness _ x⃗ → Witness _ (x ∷ x⃗)
    H (m , Hm) (o , Ho) = m + o , ∈map[×]-intro H1 H2 where
      H1 : x ∈ᴸ f (m + o)
      H1 = cum-≤→⊆ cum m≤m+n Hm
      H2 : x⃗ ∈ᴸ combine (f (m + o)) _
      H2 = combine-≤→⊆ cum m≤n+m Ho
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/ListView/Base.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Function.Enumeration.ListView.Base.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.enumeration.listview.base)  
> 交流Q群: 893531731
