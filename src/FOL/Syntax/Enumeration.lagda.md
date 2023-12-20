---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ 公式的枚举

本篇的目标是构造公式的[普通视角枚举函数](https://www.yuque.com/ocau/metalogic/foundation.enumeration.plainview) `formulaₙ : ℕ → Formula`, 满足对任意 `φ : Formula` 都存在 `n : ℕ` 使得 `formulaₙ n ≡ φ`.

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder
import Foundation.Function.Enumeration.PlainView as Plain

open import FOL.Language
module FOL.Syntax.Enumeration (ℒ : Language) where
open import FOL.Syntax.Base ℒ
open import FOL.Syntax.Discrete ℒ
instance _ = ℒ
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
- 第零项是空列表.
- 项是上一项并上 `[ # n ]` 以及一些 `f : 𝓕` 的所有 `e n` 应用. 其中一些 `f : 𝓕` 是指函数符号的枚举函数 `enum` (由语言的定义, 函数符号集 `𝓕` 可枚举) 应用于 `n` 所输出的那些 `f : 𝓕`.

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
  由语言的定义, 函数符号集 `𝓕` 可枚举. 由元语言的知识, 项的 `∣ f ∣ᶠ` 维向量 `t⃗` 可枚举. 分别取它们的见证 `m` 和 `n`, 那么 `suc m + n` 就是 `f $̇ t⃗` 的见证.

```agda
    w : ∀ t → e witness t
    w = term-elim H# H$̇ where
      H# : ∀ n → e witness # n
      H# n = ex (suc n) $ ∈-++⁺ʳ (here refl)
      H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → e witness t) → e witness (f $̇ t⃗)
      H$̇ f t⃗ IH = 𝟙.map2 H (wit f) (combine-wit c t⃗ IH) where
        H : Witness _ f → Witness _ t⃗ → Witness e (f $̇ t⃗)
        H (m , Hm) (n , Hn) = suc m + n , ∈-++⁺ʳ (there $ ∈-concat⁺′ H1 H2) where
          H1 : f $̇ t⃗ ∈ᴸ apps (m + n) f
          H1 = ∈map-intro (combine-≤→⊆ c m≤n+m Hn) refl
          H2 : apps (m + n) f ∈ᴸ map (apps (m + n)) (enum (m + n))
          H2 = ∈map-intro (cum-≤→⊆ cum m≤m+n Hm) refl
```

## 公式的枚举

```agda
instance
  enumFormula : Enum Formula
  enumFormula = mkEnum e c w where
```

```agda
    apps : ℕ → 𝓡 → 𝕃 Formula
    apps n R = map (R $̇_) (enum n)

    e : 𝕃ₙ Formula
    e zero = [ ⊥̇ ]
    e (suc n) = e n
      ++ map ∀̇_ (e n)
      ++ map (uncurry _→̇_) (e n [×] e n)
      ++ concat (map (apps n) (enum n))
```

```agda
    c : Cumulation e
    c _ = _ , refl
```

```agda
    w : ∀ φ → e witness φ
    w ⊥̇ = ex 0 (here refl)
    w (∀̇ φ) = 𝟙.map H (w φ) where
      H : Witness e φ → Witness e (∀̇ φ)
      H (n , Hn) = suc n , (∈-++⁺ʳ $ ∈-++⁺ˡ $ ∈map-intro Hn refl)
    w (φ →̇ ψ) = 𝟙.map2 H (w φ) (w ψ) where
      H : Witness e φ → Witness e ψ → Witness e (φ →̇ ψ)
      H (m , Hm) (n , Hn) = suc m + n , (∈-++⁺ʳ $ ∈-++⁺ʳ $ ∈-++⁺ˡ $ ∈map[×]-intro
        (cum-≤→⊆ c m≤m+n Hm) (cum-≤→⊆ c m≤n+m Hn))
    w (R $̇ t⃗) = 𝟙.map2 H (wit R) (wit t⃗) where
      H : Witness enum R → Witness enum t⃗ → Witness e (R $̇ t⃗)
      H (m , Hm) (n , Hn) = suc m + n , (∈-++⁺ʳ $ ∈-++⁺ʳ $ ∈-++⁺ʳ $ ∈-concat⁺′ H1 H2) where
          H1 : R $̇ t⃗ ∈ᴸ apps (m + n) R
          H1 = ∈map-intro (cum-≤→⊆ cum m≤n+m Hn) refl
          H2 : apps (m + n) R ∈ᴸ map (apps (m + n)) (enum (m + n))
          H2 = ∈map-intro (cum-≤→⊆ cum m≤m+n Hm) refl
```

```agda
enumFormula-proper : ∀ n → length (enum ⦃ enumFormula ⦄ n) > n
enumFormula-proper zero = ≤-refl
enumFormula-proper (suc n) = subst (_> _) (length-++-++ _ _) (<-≤-trans H m≤m+n) where
  H : length (enum n) + length (map ∀̇_ _) > 1 + n
  H = +-mono-≤-< (cum-length cum z≤n) (subst (_ <_) (length-map _ _) (enumFormula-proper n))
```

```agda
formulaₙ : ℕ → Formula
formulaₙ = Plain.enum enumFormula-proper

formulaₙ-wit : ∀ φ → ∃ n ， formulaₙ n ≡ φ
formulaₙ-wit = Plain.wit enumFormula-proper
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
