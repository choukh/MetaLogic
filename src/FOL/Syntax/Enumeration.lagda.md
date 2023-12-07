---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 公式的枚举

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.Enumeration (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
instance _ = ℒ
```

## 向量的枚举

```agda
combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (λ (x , x⃗) → x ∷ x⃗) (xs [×] combine xs n)
```

```agda
combine-wit : {f : 𝕃ₙ A} → Cumulation f → {n : ℕ} (x⃗ : 𝕍 A n) →
  (∀ x → x ∈⃗ x⃗ → f witness x) → (λ m → combine (f m) n) witness x⃗
combine-wit cum [] _ = ex 0 (here refl)
combine-wit cum (x ∷ x⃗) H = {! 𝟙.rec  !}
```

## 项的枚举

```agda
instance
  enumTerm : Enum Term
  enumTerm = mkEnum e c w where
```

```agda
    e : 𝕃ₙ Term
    e zero = []
    e (suc n) = e n ++ # n ∷ concat (map apps (enum n)) where
      apps : 𝓕 → 𝕃 Term
      apps f = map (f $̇_) (combine (e n) ∣ f ∣ᶠ)
```

```agda
    c : Cumulation e
    c _ = _ , refl
```

```agda
    w : ∀ t → e witness t
    w = term-elim
      (λ n → ex (suc n) (∈-++⁺ʳ (e n) (here refl)))
      (λ f t⃗ IH → {!   !})
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
