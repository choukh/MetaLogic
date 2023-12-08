---
url: foundation.selective.enumerability
---

# 元语言 ▸ 特定主题 ▸ᐞ 可枚举性

## 可选值序列视角

**<u>定义</u>** `A` 可枚举, 当且仅当存在函数 `f : ℕ → A ⊎ ⊤`, 使得对任意 `x : A`, 存在 `n` 满足 `f n ≡ x`.

**<u>定理</u> `discr→enum→count`** 如果 `A` 离散 (这意味着 `A` 是集合), 并且 `A` 可枚举, 那么 `A` 可数.

## 累积列表视角

**<u>定义</u>** 列表的无穷序列 `f : 𝕃ₙ A` 的一个累积, 记作 `Cumulation f`, 是一个以 `n : ℕ` 为索引的集族, 对每个 `n` 都给出了一个 `xs : 𝕃 A`, 使得 `f n ≡ f m ++ xs` 成立. 其中 `_++_` 是列表的拼接操作.

**<u>定义</u>** 列表的无穷序列 `f : 𝕃ₙ A` 的一个累积, 记作 `Cumulation f`, 是一个以 `n : ℕ` 为索引的集族, 对每个 `n` 都给出了一个 `xs : 𝕃 A`, 使得 `f n ≡ f m ++ xs` 成立. 其中 `_++_` 是列表的拼接操作.

**<u>定义</u>** 见证集和见证条件

- 见证集: 给定无穷序列 `f : 𝕃ₙ A` 和 `x : A`, 满足 `x ∈ᴸ enum n` 的所有 `n` 组成的集合叫做 `x` 在 `f` 中的见证集, 记作 `Witness f x`.  
- 见证条件: 我们说无穷序列 `f : 𝕃ₙ A` 见证了 `x : A`, 记作 `f witness x`, 当且仅当存在 `n` 满足 `x ∈ᴸ enum n`, 也即 `∥ Witness f x ∥₁` 成立.

**<u>定义</u>** `A` 的枚举 `Enum A` 是一个二元组

1. “见证了所有 `x : A`” (该条件记作 `wit`) 的列表无穷序列 `enum : 𝕃ₙ A`
2. `f` 的一个累积 `cum : Cumulation f`

## 普通序列视角

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Unary/Enumerable.md) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.selective.enumerability)  
> 交流Q群: 893531731
