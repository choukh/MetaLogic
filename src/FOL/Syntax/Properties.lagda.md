---
url: fol.syntax.properties
---

# 一阶逻辑 ▸ 语法 ▸⁻ 性质

这是一篇标题中带上标减号 (⁻) 的章节. 这表示这种章节不推荐线性阅读, 读者应该在需要时再回来查看. 因为这种章节只是一些枯燥引理及其证明的简单罗列, 而不包含动机的说明. 读者应该在使用这些引理的章节中寻找动机.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.Properties (ℒ : Language) where

open import FOL.Syntax ℒ
```

**<u>引理</u>** 项的归纳法: 任意给定项的性质 `P`, 可以证明任意项都满足 `P`, 只要证明以下两点

1. `P` 对所有变元成立
2. `P` 对所有形如 `f $̇ t⃗` 的项成立, 只要 `P` 对所有 `t ∈⃗ t⃗` 成立

**<u>递归证明</u>** 对项的结构归纳, 分两种情况

- 当项是变元时, 由前提1即证
- 当项是函数应用 `f $̇ t⃗` 时, 由前提2, 只要证 `P` 对所有 `t ∈⃗ t⃗` 成立, 把它视作一个内部引理, 命名为 `H`. 我们递归证明 `H`, 给定 `t ∈⃗ t⃗`, 又分两种情况
  - 当 `t` 位于 `t⃗` 的头部时, 用项的归纳法即证
  - 当 `t` 位于 `t⃗` 的尾部时, 递归使用 `H` 即证 ∎

```agda
term-elim : {P : Term → 𝕋 ℓ} → (∀ n → P (# n)) →
  (∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → P t) → P (f $̇ t⃗)) → ∀ t → P t
term-elim H1 H2 (# n) = H1 n
term-elim {P} H1 H2 (f $̇ t⃗) = H2 f t⃗ H where
  H : ∀ {n} {t⃗ : 𝕍 Term n} t → t ∈⃗ t⃗ → P t
  H t (here refl) = term-elim H1 H2 t
  H t (there t∈⃗t⃗) = H t t∈⃗t⃗
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Properties.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Properties.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.properties)  
> 交流Q群: 893531731
 