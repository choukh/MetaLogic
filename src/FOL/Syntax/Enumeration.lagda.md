---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ 公式的枚举

本篇的目标是构造公式的[普通视角枚举函数](https://www.yuque.com/ocau/metalogic/foundation.enumeration.plainview) `Ψ : ℕ → Formula`, 满足对任意 `φ : Formula` 都存在 `n : ℕ` 使得 `Ψ n ≡ φ`.

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.List.SetTheoretic renaming (_∈_ to _∈ᴸ_)
open import Foundation.Function.Enumeration.PlainView

open import FOL.Language
module FOL.Syntax.Enumeration (ℒ : Language) where
open import FOL.Syntax.Base ℒ
open import FOL.Syntax.Discrete ℒ
open import FOL.Syntax.FreshVariables ℒ
instance _ = ℒ

private variable
  m n o : ℕ
```

## 项的枚举

**<u>实例/构造</u>** 项的枚举由以下 `e`, `c`, `w` 三部分构成:

```agda
instance
  enumTerm : Enum Term
  enumTerm = mkEnum e c w where
```

### 1. 项的列表的无穷序列 `e`

我们需要同时互递归构造某函数 `f : 𝓕` 的所有 `e n` 应用, 记作 `apps n f`, 它是 `f` 应用于 `e n` 的所有 `∣ f ∣ᶠ` 维组合所得到的那些项所组成的列表.

```agda
    e : 𝕃ₙ Term
    apps : ℕ → 𝓕 → 𝕃 Term
    apps n f = map (f $̇_) (combine (e n) ∣ f ∣ᶠ)
```

我们递归定义 `e` 如下:
- 输入 `zero` 时, 输出空列表.
- 输入 `suc n` 时, 输出 `e n` 并上 `[ # n ]`, 再并上以*一些* `f : 𝓕` 为下标的集族 `apps n` 的并 (`concat`). 其中*一些* `f : 𝓕` 是指函数符号的枚举函数 `enum` (由语言的定义, 函数符号集 `𝓕` 可枚举) 应用于 `n` 所输出的那些 `f`.

此定义用传统集合论符号可表述为

$$
\begin{align*}
e(0) &= \emptyset\\
e(n^+) &= e(n) \cup \{\#n\} \cup \bigcup\{ apps(n, f) \mid f \in enum(n) \}
\end{align*}
$$

```agda
    e zero = []
    e (suc n) = e n ++ # n ∷ concat (map (apps n) (enum n))
```

### 2. `e` 的累积 `c`

由 `e` 的定义立即可得其累积.

```agda
    c : Cumulation e
    c _ = _ , refl
```

### 3. 命题 `w` : `e` 见证了任意项 `t`

我们用项的结构归纳法证明 `w`:

- 要证 `e` 见证了任意变元. 观察 `e` 的定义, 显然成立.
- 要证 `e` 见证了任意函数应用 `f $̇ t⃗`, 已知 `t⃗` 中的项都被 `e` 见证 (归纳假设).
  - 由语言的定义, 函数符号集 `𝓕` 可枚举; 由元语言的知识, 项的 `∣ f ∣ᶠ` 维向量可枚举.
    由归纳假设和涉及列表组合的引理 `combine-wit`, 只要构造一个从 `f` 的见证和 `t⃗` 的见证到 `f $̇ t⃗` 的见证的转换函数, 就证明了 `e` 见证 `f $̇ t⃗`.
    - 分别取 `f` 和 `t⃗` 的见证 `m` 和 `n`. 由枚举函数的累积性, `m + n` 也是 `f` 和 `t⃗` 的见证. 所以由 `e` 的定义, `suc m + n` 见证了 `f $̇ t⃗`. ∎

```agda
    w : ∀ t → e witness t
    w = term-elim H# H$̇ where
      H# : ∀ n → e witness # n
      H# n = ex (suc n) $ ∈++-introʳ (here refl)
      H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → e witness t) → e witness (f $̇ t⃗)
      H$̇ f t⃗ IH = 𝟙.map2 H (wit f) (combine-wit c t⃗ IH) where
        H : Witness _ f → Witness _ t⃗ → Witness _ (f $̇ t⃗)
        H (m , Hm) (n , Hn) = suc m + n , ∈++-introʳ (there $ ∈concat-intro H1 H2) where
          H1 : f $̇ t⃗ ∈ᴸ apps (m + n) f
          H1 = ∈map-intro (combine-≤→⊆ c m≤n+m Hn) refl
          H2 : apps (m + n) f ∈ᴸ map (apps (m + n)) (enum (m + n))
          H2 = ∈map-intro (cum-≤→⊆ cum m≤m+n Hm) refl
```

## 公式的枚举

**<u>定义</u>** 某关系 `R : 𝓡` 的所有 `n`-阶应用, 记作 `apps n R`, 定义为 `R` 应用于项的*一些* `∣ R ∣ᴿ` 维向量所得到的公式所组成的列表. 其中项的*一些* `∣ R ∣ᴿ` 维向量是指项的`∣ R ∣ᴿ` 维向量枚举函数 `enum` (由于项可枚举, 所以项的固定维向量也可枚举) 应用于 `n` 所输出的那些向量.

```agda
private
  apps : ℕ → 𝓡 → 𝕃 Formula
  apps n R = map (R $̇_) (enum n)
```

**<u>实例/构造</u>** 公式的枚举由以下 `e`, `c`, `w` 三部分构成:

```agda
instance
  enumFormula : Enum Formula
  enumFormula = mkEnum e c w where
```

### 1. 公式的列表的无穷序列 `e`

递归定义 `e` 如下:

- 输入 `zero` 时, 输出 `[ ⊥̇ ]`.
- 输入 `suc n` 时, 输出 `e n` 并上由 `e n` 中公式产生的所有全称量化式和所有蕴含式, 以及*一些* `R : 𝓡` 的所有 `n`-阶应用. 其中*一些* `R : 𝓡` 是指关系符号的枚举函数 `enum` (由语言的定义, 关系符号集 `𝓡` 可枚举) 应用于 `n` 所输出的那些 `R : 𝓡`.

```agda
    e : 𝕃ₙ Formula
    e zero = [ ⊥̇ ]
    e (suc n) = e n
      ++ map ∀̇_ (e n)
      ++ map (uncurry _→̇_) (e n [×] e n)
      ++ concat (map (apps n) (enum n))
```

### 2. `e` 的累积 `c`

由 `e` 的定义立即可得其累积.

```agda
    c : Cumulation e
    c _ = _ , refl
```

### 3. 命题 `w` : `e` 见证了任意公式 `φ`

由 `e` 的定义, 显然, `e` 见证了 `⊥̇`, 以及任意全称量化式和蕴含式. 而对于关系应用, 使用与项的枚举函数见证所有函数应用类似的方法可证. ∎

```agda
    w : ∀ φ → e witness φ
    w ⊥̇ = ex 0 (here refl)
    w (∀̇ φ) = 𝟙.map H (w φ) where
      H : Witness e φ → Witness e (∀̇ φ)
      H (n , Hn) = suc n , (∈++-introʳ $ ∈++-introˡ $ ∈map-intro Hn refl)
    w (φ →̇ ψ) = 𝟙.map2 H (w φ) (w ψ) where
      H : Witness e φ → Witness e ψ → Witness e (φ →̇ ψ)
      H (m , Hm) (n , Hn) = suc m + n , (∈++-introʳ $ ∈++-introʳ $ ∈++-introˡ $ ∈map[×]-intro
        (cum-≤→⊆ c m≤m+n Hm) (cum-≤→⊆ c m≤n+m Hn))
    w (R $̇ t⃗) = 𝟙.map2 H (wit R) (wit t⃗) where
      H : Witness enum R → Witness enum t⃗ → Witness e (R $̇ t⃗)
      H (m , Hm) (n , Hn) = suc m + n , (∈++-introʳ $ ∈++-introʳ $ ∈++-introʳ $ ∈concat-intro H1 H2) where
          H1 : R $̇ t⃗ ∈ᴸ apps (m + n) R
          H1 = ∈map-intro (cum-≤→⊆ cum m≤n+m Hn) refl
          H2 : apps (m + n) R ∈ᴸ map (apps (m + n)) (enum (m + n))
          H2 = ∈map-intro (cum-≤→⊆ cum m≤m+n Hm) refl
```

**<u>引理</u>** 公式的累积列表是真累积.  
**<u>证明</u>** 观察定义不难看出列表的长度是严格递增的. ∎

```agda
enumFormula-proper : ∀ n → length (enum ⦃ enumFormula ⦄ n) > n
enumFormula-proper zero = ≤-refl
enumFormula-proper (suc n) = subst (_> _) (length-++-++ _ _) (<-≤-trans H m≤m+n) where
  H : length (enum n) + length (map ∀̇_ _) > 1 + n
  H = +-mono-≤-< (cum-length cum z≤n) (subst (_ <_) (length-map _ _) (enumFormula-proper n))
```

**<u>定理</u>** 存在公式的枚举函数 `Ψ : ℕ → Formula`, 满足对任意 `φ : Formula` 都存在 `n : ℕ` 使得 `Ψ n ≡ φ`.  
**<u>证明</u>** 由于公式类型 `Formula` 是离散集且可枚举, 且其中的累积列表是真累积, 符合普通视角枚举函数 `Plain.enum` 的要求, 按其定义构造即得符合要求的 `Ψ : ℕ → Formula`. ∎

```agda
module Plain = PlainEnum enumFormula-proper

Ψ : ℕ → Formula
Ψ = Plain.enum

Ψ-wit : ∀ φ → ∃ n ， Ψ n ≡ φ
Ψ-wit = Plain.wit
```

## 枚举物的新变元

公式的枚举函数 `Ψ` 有一个非常显然的性质: 对任意 `m ≤ n`, `# n` 是 `Ψ m` 的新变元 (`Ψ-fresh`). 因为变元的数量是无限的, 而任一时刻只有有限个被枚举出来. 然而完整地写出其形式化证明却相当冗长且乏味, 因为必须对枚举函数的结构一步步地归纳. 比较适合处理这种情况的是 Coq 和 Lean 等自带 tactic 的证明助理. 虽然 Agda 也可以使用反射机制实现 tactic, 但毕竟需要额外去实现, 除非后面经常出现这种情况, 否则暂不考虑.

```agda
termEnum-fresh : m ≤ n → t ∈ᴸ enum m → freshₜ n t
termEnum-fresh {suc m} le t∈ with ∈++-elim _ t∈
... | inj₁ t∈ = termEnum-fresh (m+n≤o⇒n≤o 1 le) t∈
... | inj₂ (here refl) = fresh# λ { refl → 1+n≰n le }
termEnum-fresh {t = # o} _ _
    | inj₂ (there t∈) with ∈concat-elim _ t∈
...   | _ , t∈ts , ts∈ with ∈map-elim ts∈
...     | _ , _ , refl with ∈map-elim t∈ts
...       | _ , _ , ()
termEnum-fresh {t = f $̇ t⃗} le _
    | inj₂ (there t∈) with ∈concat-elim _ t∈
...   | _ , t∈ts , ts∈ with ∈map-elim ts∈
...     | _ , _ , refl with ∈map-elim t∈ts
...       | _ , t⃗∈ , refl with ∈combine-elim t⃗∈
...         | H = fresh$̇ λ t t∈t⃗ → termEnum-fresh (m+n≤o⇒n≤o 1 le) (H t∈t⃗)

termEnum-fresh-vec : m ≤ n → {t⃗ : 𝕍 Term o} → t⃗ ∈ᴸ enum m → ∀ {t} → t ∈⃗ t⃗ → freshₜ n t
termEnum-fresh-vec {suc m} le t⃗∈ᴸ t∈⃗ with ∈++-elim _ t⃗∈ᴸ
... | inj₁ t⃗∈ᴸ = termEnum-fresh-vec (m+n≤o⇒n≤o 1 le) t⃗∈ᴸ t∈⃗
... | inj₂ t⃗∈ᴸ = termEnum-fresh (m+n≤o⇒n≤o 1 le) (∈combine-elim t⃗∈ᴸ t∈⃗)

formulaEnum-fresh : m ≤ n → φ ∈ᴸ enum m → freshᵩ n φ
formulaEnum-fresh {(zero)} _ (here refl) = fresh⊥̇
formulaEnum-fresh {suc m} {φ = ⊥̇} le φ∈ = fresh⊥̇

formulaEnum-fresh {suc m} {φ = ∀̇ φ} le φ∈ with ∈++-elim _ φ∈
... | inj₁ φ∈e = formulaEnum-fresh (m+n≤o⇒n≤o 1 le) φ∈e
... | inj₂ φ∈++ with ∈++-elim _ φ∈++
...   | inj₁ φ∈∀̇ with ∈map-elim φ∈∀̇
...     | _ , φ∈e , refl = fresh∀̇ $ formulaEnum-fresh (≤-trans (m+n≤o⇒n≤o 1 le) m≤n+m) φ∈e
formulaEnum-fresh _ _ | _
      | inj₂ φ∈++ with ∈++-elim _ φ∈++
...     | inj₁ φ∈→̇ with ∈map-elim φ∈→̇
...       | _ , _ , ()
formulaEnum-fresh _ _ | _ | _
        | inj₂ φ∈$̇ with ∈concat-elim _ φ∈$̇
...       | _ , φ∈φs , φs∈ with ∈map-elim φs∈
...         | _ , _ , eq with ∈map-elim $ subst (_ ∈ᴸ_) (sym eq) φ∈φs
...           | _ , _ , ()

formulaEnum-fresh {suc m} {φ = φ →̇ ψ} le φ∈ with ∈++-elim _ φ∈
... | inj₁ φ∈e = formulaEnum-fresh (m+n≤o⇒n≤o 1 le) φ∈e
... | inj₂ φ∈++ with ∈++-elim _ φ∈++
...   | inj₁ φ∈∀̇ with ∈map-elim φ∈∀̇
...     | _ , _ , ()
formulaEnum-fresh le _ | _
      | inj₂ φ∈++ with ∈++-elim _ φ∈++
...     | inj₁ φ∈→̇ with ∈map-elim φ∈→̇
...       | _ , φ∈× , refl with ∈[×]-elim φ∈×
...         | φ∈e₁ , φ∈e₂ = let H = ≤-trans (m+n≤o⇒n≤o 1 le) m≤n+m in
              fresh→̇ (formulaEnum-fresh H φ∈e₁) (formulaEnum-fresh H φ∈e₂)
formulaEnum-fresh _ _ | _ | _
        | inj₂ φ∈$̇ with ∈concat-elim _ φ∈$̇
...       | _ , φ∈φs , φs∈ with ∈map-elim φs∈
...         | _ , _ , eq with ∈map-elim $ subst (_ ∈ᴸ_) (sym eq) φ∈φs
...           | _ , _ , ()

formulaEnum-fresh {suc m} {φ = R $̇ t⃗} le φ∈ with ∈++-elim _ φ∈
... | inj₁ φ∈e = formulaEnum-fresh (m+n≤o⇒n≤o 1 le) φ∈e
... | inj₂ φ∈++ with ∈++-elim _ φ∈++
...   | inj₁ φ∈∀̇ with ∈map-elim φ∈∀̇
...     | _ , _ , ()
formulaEnum-fresh le _ | _
      | inj₂ φ∈++ with ∈++-elim _ φ∈++
...     | inj₁ φ∈→̇ with ∈map-elim φ∈→̇
...       | _ , _ , ()
formulaEnum-fresh {suc m} {φ = R $̇ t⃗} le _ | _ | _
        | inj₂ φ∈$̇ = H (m+n≤o⇒n≤o 1 le) φ∈$̇ where
  H : m ≤ n → φ ∈ᴸ concat (map (apps m) (enum m)) → freshᵩ n φ
  H le φ∈$̇ with ∈concat-elim _ φ∈$̇
  ... | _ , φ∈φs , φs∈ with ∈map-elim φs∈
  ...   | _ , _ , refl with ∈map-elim φ∈φs
  ...     | _ , t⃗∈ , refl = fresh$̇ λ _ t∈t⃗ → termEnum-fresh-vec le t⃗∈ t∈t⃗

Ψ-fresh : m ≤ n → freshᵩ n (Ψ m)
Ψ-fresh le = formulaEnum-fresh le Plain.cum
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
