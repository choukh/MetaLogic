---
url: foundation.discrete.list
---

# 元语言 ▸ 离散性 ▸ 列表

由离散集合的元素组成的列表, 简称离散列表, 具有一些特殊性质, 我们把它们收集到本章.

```agda
open import Foundation.Prelude
open import Foundation.Relation.Nullary.Discrete.Base
module Foundation.Relation.Nullary.Discrete.List ⦃ dA : discrete A ⦄ where
```

我们需要以下模块的相关内容:

- `Empty` 模块: 归谬法 `exfalso`
- `Bool` 模块: if赋值句 `if_then_else_ : Bool → A → A → A`
- `Decidable` 模块: 判定结果的布尔值提取函数 `does : Dec A → Bool`

```agda
open import Foundation.Data.Empty
open import Foundation.Data.Bool
open import Foundation.Data.Maybe
open import Foundation.Data.Sigma
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic
open import Foundation.Relation.Nullary.Decidable
```

我们使用以下隐式参数

```agda
private variable
  n : ℕ
  x y : A
  xs : 𝕃 A
```

## 成员可判定

**<u>算法</u>** 判定 `x` 在不在列表 `xs` 中:

- 当列表为空时, 显然不在.
- 当列表为 `y ∷ xs` 时, 判定 `x ≟ y`.
  - 若相等, 则在.
  - 若不相等, 递归地在 `xs` 中寻找. ∎

```agda
infix 4 _∈?_
_∈?_ : (x : A) (xs : 𝕃 A) → Dec (x ∈ xs)
x ∈? [] = no λ ()
x ∈? (y ∷ xs) with x ≟ y
... | yes refl = yes (here refl)
... | no x≢y with x ∈? xs
... | yes x∈xs = yes (there x∈xs)
... | no x∉xs = no λ { (here refl) → x≢y refl
                     ; (there x∈xs) → x∉xs x∈xs }
```

## 逆索引

**<u>算法</u>** 列表 `xs` 中指定元素 `x` 的索引, 记作 `xs [ x ]⁻¹?`, 计算如下

- 当列表为空时, 返回 `none`, 即列表中不存在 `x`.
- 当列表为 `y ∷ xs` 时, 判定 `x ≟ y` (由于我们讨论的是离散列表, 所以这一步是可行的).
  - 若相等 (`x` 在列表头部), 则返回 `0`.
  - 若不相等 (`x` 可能在列表尾部), 则递归地在 `xs` 中寻找 `x` 的索引, 并将结果加一. ∎

```agda
_[_]⁻¹? : 𝕃 A → A → ℕ ？
[] [ x ]⁻¹? = none
(y ∷ xs) [ x ]⁻¹? = if does (x ≟ y) then some 0 else rec where
  rec : ℕ ？
  rec with xs [ x ]⁻¹?
  ... | some n = some (suc n)
  ... | none = none
```

**<u>引理</u>** 给出 `x ∈ xs` 的证据, 则 `xs [ x ]⁻¹?` 可以取到 (`some` 形式的) 值, 计算如下

- 若 `x` 在 `xs` 的头部, 则其索引为 `0`.
- 否则 `x` 必在 `xs` 的尾部, 将该证据递归地输入到本算法中, 可知 `x` 在尾部必有索引 `n`, 所以 `x` 在 `xs` 中必有索引 `suc n`. ∎

```agda
some[]⁻¹-intro : x ∈ xs → Σ n ， xs [ x ]⁻¹? ≡ some n
some[]⁻¹-intro {x} {y ∷ xs} _ with x ≟ y
...                           | yes _ = 0 , refl
some[]⁻¹-intro (here p)       | no ¬p = exfalso (¬p p)
some[]⁻¹-intro (there x∈)     | no _ with some[]⁻¹-intro x∈
... | n , H rewrite H = suc n , refl
```

**<u>引理</u>** 如果 `xs [ x ]⁻¹?` 可以取到 (`some` 形式的) 值, 那么 `x ∈ xs`. 对 `xs` 的长度归纳.

- `xs` 不可能为空.
- 当 `xs` 为 `y ∷ xs` 时, 判定 `x ≟ y`.
  - 若相等, 则 `x` 在 `y ∷ xs` 的头部.
  - 若不相等, 此时有 `xs [ x ]⁻¹? ≡ some n`, 所以 `x` 在 `y ∷ xs` 的尾部. ∎

```agda
some[]⁻¹-elim : ∀ n → xs [ x ]⁻¹? ≡ some n → x ∈ xs
some[]⁻¹-elim {y ∷ xs} {x} n H with x ≟ y | xs [ x ]⁻¹? in eq
... | yes refl | _      = here refl
... | no ¬p    | some _ = there (some[]⁻¹-elim _ eq)
```

**<u>引理</u>** 如果 `xs [ x ]⁻¹?` 可以算出为 `n`, 则 `xs [ n ]?` 可以算出为 `x`.  
**<u>证明</u>** 计算即得. ∎

```agda
some[]⁻¹→some[] : (xs : 𝕃 A) → xs [ x ]⁻¹? ≡ some n → xs [ n ]? ≡ some x
some[]⁻¹→some[] {x} (y ∷ xs) H with x ≟ y | xs [ x ]⁻¹? in eq
some[]⁻¹→some[] _        refl  | yes refl | _      = refl
some[]⁻¹→some[] (y ∷ xs) refl  | no _     | some _ = some[]⁻¹→some[] xs eq
```

## 元素的移除

**<u>定义</u>** 将列表中 `xs` 中与 `x` 相等的元素全部去掉, 所得到的集合叫做 `xs` 移除 `x`, 记作 `remove xs x`.

```
remove : 𝕃 A → A → 𝕃 A
remove xs x = filter {P = _≢ x} (λ _ → ¬? it) xs
```

**<u>引理</u>** 移除的引入和消去.

```agda
∈remove-intro : x ∈ xs → x ≢ y → x ∈ remove xs y
∈remove-intro = ∈filter-intro (λ _ → ¬? it)

∈remove-elim : x ∈ remove xs y → x ∈ xs × x ≢ y
∈remove-elim = ∈filter-elim (λ _ → ¬? it)
```

**<u>引理</u>** 移除元素后的列表包含于原列表.

```agda
remove⊆ : remove xs x ⊆ xs
remove⊆ x∈ = ∈remove-elim x∈ .fst
```

**<u>引理</u>** `y ∷ xs ⊆ y ∷ remove xs y`.

```agda
∷⊆∷remove : y ∷ xs ⊆ y ∷ remove xs y
∷⊆∷remove (here refl) = here refl
∷⊆∷remove {y} {x} (there x∈) with x ≟ y
... | yes refl = here refl
... | no x≢y = there (∈remove-intro x∈ x≢y)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Nullary/Discrete/List.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Relation.Nullary.Discrete.List.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.discrete.list)  
> 交流Q群: 893531731
