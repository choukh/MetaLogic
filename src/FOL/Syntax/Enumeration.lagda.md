---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 公式的枚举

```agda
open import Foundation.Essential
open import FOL.Language

module FOL.Syntax.Enumeration
  (ℒ @ (mkLang 𝓕 𝓡 ∣_∣ᶠ ∣_∣ᴿ _ _ (𝓕-enum , 𝓕-cum , 𝓕-wit) (𝓡-enum , 𝓡-cum , 𝓡-wit)) : Language)
  where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
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
combine-wit = {!   !}
```

## 项的枚举

```agda
term-enum : 𝕃ₙ Term
term-enum zero = []
term-enum (suc n) = term-enum n ++ # n ∷ concat (map apps (𝓕-enum n)) where
  apps : 𝓕 → 𝕃 Term
  apps f = map (f $̇_) (combine (term-enum n) ∣ f ∣ᶠ)
```

```agda
term-cum : Cumulation term-enum
term-cum _ = _ , refl
```

```agda
term-wit : ∀ t → term-enum witness t
term-wit = term-elim
  (λ n → ex (suc n) (∈-++⁺ʳ (term-enum n) (here refl)))
  (λ f t⃗ IH → {!   !})
```

```agda
enumTerm : Enum Term
enumTerm = term-enum , term-cum , term-wit
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
 