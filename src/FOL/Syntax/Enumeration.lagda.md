---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 公式的枚举

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder
open import Enumerability.ListView

open import FOL.Language
module FOL.Syntax.Enumeration (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
instance _ = ℒ
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
