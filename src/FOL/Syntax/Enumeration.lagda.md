---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 公式的枚举

```agda
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
combine-wit {f} cum (x ∷ x⃗) H0 = 𝟙.map2 H (H0 x (here refl)) IH where
    IH = combine-wit cum x⃗ λ y y∈⃗ → H0 y (there y∈⃗)
    H : Witness f x → Witness _ x⃗ → Witness _ (x ∷ x⃗)
    H (m , Hm) (o , Ho) = m + o , ∈map-intro (∈[×]-intro H1 H2) refl where
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
      H (m , Hm) (suc n , Hn) = suc m + suc n , ∈-++⁺ʳ _ (∈map-intro (∈[×]-intro H1 H2) refl) where
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
      H# n = ex (suc n) $ ∈-++⁺ʳ (e n) (here refl)
      H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → e witness t) → e witness (f $̇ t⃗)
      H$̇ f t⃗ IH = 𝟙.map2 H (combine-wit c t⃗ IH) (wit f) where
        H : Witness _ t⃗ → Witness enum f → Witness e (f $̇ t⃗)
        H (m , Hm) (n , Hn) = suc m + n , ∈-++⁺ʳ (e (m + n)) (there $ ∈-concat⁺′ H1 H2) where
          H1 : f $̇ t⃗ ∈ᴸ apps (m + n) f
          H1 = ∈map-intro (combine-≤→⊆ {m = m} c m≤m+n Hm) refl
          H2 : apps (m + n) f ∈ᴸ map (apps (m + n)) (enum (m + n))
          H2 = ∈map-intro (cum-≤→⊆ cum m≤n+m Hn) refl
```

## 公式的枚举

```agda
instance
  enumFormula : Enum Formula
  enumFormula = mkEnum e c (∣_∣₁ ∘ w) where
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
    w : ∀ φ → Witness e φ
    w ⊥̇ = 0 , here refl
    w (φ →̇ ψ) with w φ | w ψ
    ... | n , Hn | m , Hm = {!   !}
    w (∀̇ φ) = {!   !}
    w (R $̇ t⃗) = {!   !}
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
