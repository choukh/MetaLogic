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

## 向量的枚举

```agda
private variable
  f : 𝕃ₙ A
  m n o : ℕ
```

```agda
combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (λ (x , x⃗) → x ∷ x⃗) (xs [×] combine xs n)
```

```agda
combine-≤→⊆ : Cumulation f → m ≤ o → combine (f m) n ⊆ combine (f o) n
combine-≤→⊆ {n = zero} _ _ H = H
combine-≤→⊆ {n = suc n} cum m≤o H with ∈map-elim H
... | (x , x⃗) , ∈[×] , eq with ∈[×]-elim ∈[×]
... | H1 , H2 = ∈map-intro (∈[×]-intro (cum-≤→⊆ cum m≤o H1) (combine-≤→⊆ cum m≤o H2)) eq
```

```agda
combine-wit : Cumulation f → (x⃗ : 𝕍 A n) →
  (∀ x → x ∈⃗ x⃗ → f witness x) → (λ k → combine (f k) n) witness x⃗
combine-wit _ [] _ = ex 0 (here refl)
combine-wit {f} cum (x ∷ x⃗) H = 𝟙.intro2
  (H x (here refl))
  (combine-wit cum x⃗ λ y y∈⃗ → H y (there y∈⃗))
  λ { (m , x∈fm) (o , x⃗∈comb) →
    let H1 : x ∈ᴸ f (m + o)
        H1 = cum-≤→⊆ cum m≤m+n x∈fm
        H2 : x⃗ ∈ᴸ combine (f (m + o)) _
        H2 = combine-≤→⊆ cum m≤n+m x⃗∈comb
    in ex (m + o) $ ∈map-intro (∈[×]-intro H1 H2) refl
  }
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

    e zero = []
    e (suc n) = e n ++ # n ∷ concat (map (apps n) (enum n))
    apps n f = map (f $̇_) (combine (e n) ∣ f ∣ᶠ)
```

```agda
    c : Cumulation e
    c _ = _ , refl
```

```agda
    w : ∀ t → e witness t
    w = term-elim
      (λ n → ex (suc n) $ ∈-++⁺ʳ (e n) (here refl))
      λ f t⃗ IH → 𝟙.intro2
        (combine-wit c t⃗ IH)
        (wit f)
        λ { (n , Hn) (m , Hm) →
          let H1 : f $̇ t⃗ ∈ᴸ apps (n + m) f
              H1 = ∈map-intro (combine-≤→⊆ c m≤m+n Hn) refl
              H2 : apps (n + m) f ∈ᴸ map (apps (n + m)) (enum (n + m))
              H2 = ∈map-intro (cum-≤→⊆ cum m≤n+m Hm) refl
          in ex (suc n + m) $ ∈-++⁺ʳ (e (n + m)) $ there (∈-concat⁺′ H1 H2)
        }
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
