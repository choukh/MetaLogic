---
url: foundation.reverse
---

# 元语言 ▸ 构造主义反推数学的基本设置

```agda
module Foundation.ConstructiveReverseMath where

open import Foundation.Prelude
open import Foundation.Data.Empty
open import Foundation.Data.Bool
open import Foundation.Data.Nat
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Relation.Nullary.Negation
open import Foundation.Relation.Nullary.Decidable
```

## 非空与居留

```agda
inhabited : 𝕋 ℓ → 𝕋 ℓ
inhabited A = ∥ A ∥₁

nonEmpty : 𝕋 ℓ → 𝕋 ℓ
nonEmpty A = ¬ ¬ A
```

```agda
inhabited→nonEmpty : inhabited A → nonEmpty A
inhabited→nonEmpty = 𝟙.rec isProp¬ λ a ¬a → ¬a a
```

```agda
nonEmpty-cong : (A → B) → nonEmpty A → nonEmpty B
nonEmpty-cong ab neA ¬b = neA $ ¬b ∘ ab
```

```agda
nonEmptyInhabitation : nonEmpty A ↔ nonEmpty (inhabited A)
nonEmptyInhabitation .⇒ ¬¬a ¬∣a∣ = ¬¬a λ a → ¬∣a∣ ∣ a ∣₁
nonEmptyInhabitation .⇐ ¬¬∣a∣ = ¬¬∣a∣ ∘ 𝟙.rec isProp⊥
```

## 稳定性

```agda
stable : 𝕋 ℓ → 𝕋 ℓ
stable A = nonEmpty A → A

stable₁ : 𝕋 ℓ → 𝕋 ℓ
stable₁ A = nonEmpty A → inhabited A
```

```agda
stable-cong : A ↔ B → stable A → stable B
stable-cong iff stbA = iff .⇒ ∘ stbA ∘ nonEmpty-cong (iff .⇐)

stable₁-cong : A ↔ B → stable₁ A → stable₁ B
stable₁-cong iff stbA = 𝟙.map (iff .⇒) ∘ stbA ∘ nonEmpty-cong (iff .⇐)
```

```agda
stableInhabitation : stable₁ A ↔ stable (inhabited A)
stableInhabitation .⇒ stbA ne = stbA (nonEmptyInhabitation .⇐ ne)
stableInhabitation .⇐ stbA ne = stbA (nonEmptyInhabitation .⇒ ne)
```

## 排中律

```agda
𝗟𝗘𝗠 : 𝕋 (ℓ ⁺)
𝗟𝗘𝗠 {ℓ} = (P : 𝕋 ℓ) → isProp P → Dec P
```

```agda
Dec-nonEmpty : (P : 𝕋 ℓ) → isProp P → nonEmpty (Dec P)
Dec-nonEmpty P propP demon = demon $ no $ demon ∘ yes
```

```agda
𝗗𝗡𝗘 : 𝕋 (ℓ ⁺)
𝗗𝗡𝗘 {ℓ} = (P : 𝕋 ℓ) → isProp P → stable P
```

```agda
𝗟𝗘𝗠↔𝗗𝗡𝗘 : 𝗟𝗘𝗠 {ℓ} ↔ 𝗗𝗡𝗘 {ℓ}
𝗟𝗘𝗠↔𝗗𝗡𝗘 .⇒ lem P propP with lem P propP
... | yes p = λ _ → p
... | no ¬p = λ ¬¬p → exfalso (¬¬p ¬p)
𝗟𝗘𝗠↔𝗗𝗡𝗘 .⇐ dne P propP = dne (Dec P) (isPredDec propP) (Dec-nonEmpty P propP)
```

## 马尔可夫原理

```agda
satisfied : (ℕ → 𝔹) → 𝕋
satisfied f = ∃ n ， f n ≡ true
```

```agda
𝗠𝗣 : 𝕋
𝗠𝗣 = ∀ f → stable (satisfied f)
```

```agda

```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/ConstructiveReverseMath.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.ConstructiveReverseMath.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.reverse)  
> 交流Q群: 893531731
