---
url: fol.syntax.properties
---

# 一阶逻辑 ▸ 语法 ▸ 性质

```agda
open import Foundation.Essential
open import Foundation.Data.Vec.SetTheoretic
  renaming (_∈_ to _∈⃗_)

open import FOL.Language
module FOL.Syntax.Properties (ℒ : Language) where

open import FOL.Syntax ℒ

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
