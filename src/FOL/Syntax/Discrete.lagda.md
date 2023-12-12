---
url: fol.syntax.discrete
---

# 一阶逻辑 ▸ 语法 ▸ 公式的离散性

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.Discrete (ℒ : Language) where

open import FOL.Syntax.Base ℒ
instance _ = ℒ
```

```agda
$̇-inj : (f : 𝓕) (t⃗ s⃗ : 𝕍 Term ∣ f ∣ᶠ) → f $̇ t⃗ ≡ f $̇ s⃗ → t⃗ ≡ s⃗
$̇-inj f t⃗ s⃗ eq = {!   !}
```

```agda
instance
  discrTerm : discrete Term
  discrTerm = term-elim {P = λ t → ∀ s → Dec (t ≡ s)} H# H$̇ _ _ where
    H# : (m : ℕ) (s : Term) → Dec (# m ≡ s)
    H# m (# n) with m ≟ n
    ... | yes refl = yes refl
    ... | no ¬eq = no λ { refl → ¬eq refl }
    H# m (f $̇ t⃗) = no λ ()
    H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → ∀ s → Dec (t ≡ s)) → ∀ s → Dec ((f $̇ t⃗) ≡ s)
    H$̇ f t⃗ IH (# n) = no λ ()
    H$̇ f t⃗ IH (g $̇ s⃗) with f ≟ g
    ... | no ¬eq = no λ { refl → ¬eq refl }
    ... | yes refl with discrete𝕍-strong t⃗ s⃗ IH
    ... | yes refl = yes refl
    ... | no ¬eq = no λ eq → ¬eq ($̇-inj f t⃗ s⃗ eq)
```

```agda
instance
  discrFormula : discrete Formula
  discrFormula = {!   !}
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Discrete.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Discrete.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.discrete)  
> 交流Q群: 893531731
 