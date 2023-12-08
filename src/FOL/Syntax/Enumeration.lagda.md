---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 公式的枚举

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder

open import FOL.Language
module FOL.Syntax.Enumeration (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
instance _ = ℒ
```

## 枚举 (复习)

**<u>定义</u>** 列表的无穷序列 `f : 𝕃ₙ A` 的一个累积, 记作 `Cumulation f`, 是一个以 `n : ℕ` 为索引的集族, 对每个 `n` 都给出了一个 `xs : 𝕃 A`, 使得 `f n ≡ f m ++ xs` 成立. 其中 `_++_` 是列表的拼接操作.

**<u>定义</u>** 见证集和见证条件

- 见证集: 给定无穷序列 `f : 𝕃ₙ A` 和 `x : A`, 满足 `x ∈ᴸ enum n` 的所有 `n` 组成的集合叫做 `x` 在 `f` 中的见证集, 记作 `Witness f x`.  
- 见证条件: 我们说无穷序列 `f : 𝕃ₙ A` 见证了 `x : A`, 记作 `f witness x`, 当且仅当存在 `n` 满足 `x ∈ᴸ enum n`, 也即 `∥ Witness f x ∥₁` 成立.

**<u>定义</u>** `A` 的枚举 `Enum A` 是一个二元组

1. “见证了所有 `x : A`” (该条件记作 `wit`) 的列表无穷序列 `enum : 𝕃ₙ A`
2. `f` 的一个累积 `cum : Cumulation f`

## 向量的枚举

```agda
private variable
  f : 𝕃ₙ A
  m n o : ℕ
```

```agda
combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (uncurry _∷_) (xs [×] combine xs n)
```

```agda
combine-≤→⊆ : Cumulation f → m ≤ o → combine (f m) n ⊆ combine (f o) n
combine-≤→⊆ {n = zero} _ _ H = H
combine-≤→⊆ {n = suc n} cum m≤o H with ∈map[×]-elim H
... | x , y , x∈ , y∈ , refl = ∈map[×]-intro (cum-≤→⊆ cum m≤o x∈) (combine-≤→⊆ cum m≤o y∈)
```

```agda
combine-wit : Cumulation f → (x⃗ : 𝕍 A n) →
  (∀ x → x ∈⃗ x⃗ → f witness x) → (λ k → combine (f k) n) witness x⃗
combine-wit _ [] _ = ex 0 (here refl)
combine-wit {f} cum (x ∷ x⃗) H0 = 𝟙.map2 H (H0 x (here refl)) IH where
    IH = combine-wit cum x⃗ λ y y∈⃗ → H0 y (there y∈⃗)
    H : Witness f x → Witness _ x⃗ → Witness _ (x ∷ x⃗)
    H (m , Hm) (o , Ho) = m + o , ∈map[×]-intro H1 H2 where
      H1 : x ∈ᴸ f (m + o)
      H1 = cum-≤→⊆ cum m≤m+n Hm
      H2 : x⃗ ∈ᴸ combine (f (m + o)) _
      H2 = combine-≤→⊆ cum m≤n+m Ho
```

```agda
instance
  enumVec : ⦃ Enum A ⦄ → Enum (𝕍 A n)
  enumVec {A} = mkEnum e c w where
```

```agda
    e : 𝕃ₙ (𝕍 A n)
    e zero = []
    e {n} (suc m) = e m ++ combine (enum m) n
```

```agda
    c : Cumulation e
    c _ = _ , refl
```

```agda
    e-≤→⊆ : {x⃗ : 𝕍 A n} → m ≤ o → x⃗ ∈ᴸ e m → x⃗ ∈ᴸ combine (enum o) n
    e-≤→⊆ {m = suc m} sm≤o H with ∈-++⁻ (e m) H
    ... | inj₁ x⃗∈en   = e-≤→⊆ (m+n≤o⇒n≤o 1 sm≤o) x⃗∈en
    ... | inj₂ x⃗∈comb = combine-≤→⊆ cum (m+n≤o⇒n≤o 1 sm≤o) x⃗∈comb
```

```agda
    w : (x⃗ : 𝕍 A n) → e witness x⃗
    w [] = ex 1 (here refl)
    w (x ∷ x⃗) = 𝟙.map2 H (wit x) (w x⃗) where
      H : Witness enum x → Witness e x⃗ → Witness e (x ∷ x⃗)
      H (m , Hm) (suc n , Hn) = suc m + suc n , ∈-++⁺ʳ (∈map[×]-intro H1 H2) where
        H1 : x ∈ᴸ enum (m + suc n)
        H1 = cum-≤→⊆ cum m≤m+n Hm
        H2 : x⃗ ∈ᴸ combine (enum (m + suc n)) _
        H2 = e-≤→⊆ m≤n+m Hn
```

## 项的枚举

```agda
instance
  enumTerm : Enum Term
  enumTerm = mkEnum e c w where
```

```agda
    e : 𝕃ₙ Term
    apps : ℕ → 𝓕 → 𝕃 Term
    apps n f = map (f $̇_) (combine (e n) ∣ f ∣ᶠ)

    e zero = []
    e (suc n) = e n ++ # n ∷ concat (map (apps n) (enum n))
```

```agda
    c : Cumulation e
    c _ = _ , refl
```

```agda
    w : ∀ t → e witness t
    w = term-elim H# H$̇ where
      H# : ∀ n → e witness # n
      H# n = ex (suc n) $ ∈-++⁺ʳ (here refl)
      H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → e witness t) → e witness (f $̇ t⃗)
      H$̇ f t⃗ IH = 𝟙.map2 H (wit f) (combine-wit c t⃗ IH) where
        H : Witness enum f → Witness _ t⃗ → Witness e (f $̇ t⃗)
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
      ++ map (uncurry _→̇_) (e n [×] e n)
      ++ map ∀̇_ (e n)
      ++ concat (map (apps n) (enum n))
```

```agda
    c : Cumulation e
    c _ = _ , refl
```

```agda
    w : ∀ φ → e witness φ
    w ⊥̇ = ex 0 (here refl)
    w (φ →̇ ψ) = 𝟙.map2 H (w φ) (w ψ) where
      H : Witness e φ → Witness e ψ → Witness e (φ →̇ ψ)
      H (m , Hm) (n , Hn) = suc m + n , (∈-++⁺ʳ $ ∈-++⁺ˡ $ ∈map[×]-intro
        (cum-≤→⊆ c m≤m+n Hm) (cum-≤→⊆ c m≤n+m Hn))
    w (∀̇ φ) = 𝟙.map H (w φ) where
      H : Witness e φ → Witness e (∀̇ φ)
      H (n , Hn) = suc n , (∈-++⁺ʳ $ ∈-++⁺ʳ $ ∈-++⁺ˡ $ ∈map-intro Hn refl)
    w (R $̇ t⃗) = 𝟙.map2 H (wit R) (wit t⃗) where
      H : Witness enum R → Witness enum t⃗ → Witness e (R $̇ t⃗)
      H (m , Hm) (n , Hn) = suc m + n , (∈-++⁺ʳ $ ∈-++⁺ʳ $ ∈-++⁺ʳ $ ∈-concat⁺′ H1 H2) where
          H1 : R $̇ t⃗ ∈ᴸ apps (m + n) R
          H1 = ∈map-intro (cum-≤→⊆ cum m≤n+m Hn) refl
          H2 : apps (m + n) R ∈ᴸ map (apps (m + n)) (enum (m + n))
          H2 = ∈map-intro (cum-≤→⊆ cum m≤m+n Hm) refl
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
