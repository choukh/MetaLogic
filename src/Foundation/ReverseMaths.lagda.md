---
url: foundation.reverse
---

# 元语言 ▸ 构造主义反推基础

```agda
module Foundation.ReverseMaths where

open import Foundation.Prelude
open import Foundation.Data.Empty
open import Foundation.Data.Bool
open import Foundation.Data.Nat
open import Foundation.Data.Maybe
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Relation.Nullary.Negation
open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete.Base
open import Foundation.Relation.Nullary.Discrete.List
open import Foundation.Function.Enumeration.ListView.Base
```

## 居留与非空

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
nonEmpty-subst : (A → B) → nonEmpty A → nonEmpty B
nonEmpty-subst ab neA ¬b = neA $ ¬b ∘ ab
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
stable-subst : A ↔ B → stable A → stable B
stable-subst iff stbA = iff .⇒ ∘ stbA ∘ nonEmpty-subst (iff .⇐)

stable₁-subst : A ↔ B → stable₁ A → stable₁ B
stable₁-subst iff stbA = 𝟙.map (iff .⇒) ∘ stbA ∘ nonEmpty-subst (iff .⇐)
```

```agda
stableInhabitation : stable₁ A ↔ stable (inhabited A)
stableInhabitation .⇒ stbA ne = stbA (nonEmptyInhabitation .⇐ ne)
stableInhabitation .⇐ stbA ne = stbA (nonEmptyInhabitation .⇒ ne)
```

## 排中律

```agda
module _ {ℓ} where
```

```agda
  𝗟𝗘𝗠 : 𝕋 (ℓ ⁺)
  𝗟𝗘𝗠 = (P : 𝕋 ℓ) → isProp P → Dec P
```

```agda
  Dec-nonEmpty : (P : 𝕋 ℓ) → isProp P → nonEmpty (Dec P)
  Dec-nonEmpty P propP demon = demon $ no $ demon ∘ yes
```

```agda
  𝗗𝗡𝗘 : 𝕋 (ℓ ⁺)
  𝗗𝗡𝗘 = (P : 𝕋 ℓ) → isProp P → stable P

  𝗗𝗡𝗘₁ : 𝕋 (ℓ ⁺)
  𝗗𝗡𝗘₁ = (A : 𝕋 ℓ) → stable₁ A
```

```agda
  𝗗𝗡𝗘↔𝗗𝗡𝗘₁ : 𝗗𝗡𝗘 ↔ 𝗗𝗡𝗘₁
  𝗗𝗡𝗘↔𝗗𝗡𝗘₁ .⇒ dne A = stableInhabitation .⇐ (dne ∥ A ∥₁ 𝟙.squash)
  𝗗𝗡𝗘↔𝗗𝗡𝗘₁ .⇐ dne₁ P propP ne = 𝟙.rec propP id (dne₁ P ne)
```

```agda
  𝗟𝗘𝗠↔𝗗𝗡𝗘 : 𝗟𝗘𝗠 ↔ 𝗗𝗡𝗘
  𝗟𝗘𝗠↔𝗗𝗡𝗘 .⇒ lem P propP with lem P propP
  ... | yes p = λ _ → p
  ... | no ¬p = λ ¬¬p → exfalso (¬¬p ¬p)
  𝗟𝗘𝗠↔𝗗𝗡𝗘 .⇐ dne P propP = dne (Dec P) (isPredDec propP) (Dec-nonEmpty P propP)
```

## 半可判定

```agda
satisfied : (ℕ → 𝔹) → 𝕋
satisfied f = ∃ n ， f n ≡ true
```

```agda
SemiDec : 𝕋 ℓ → 𝕋 _
SemiDec A = Σ f ， A ↔ satisfied f
```

```agda
module _ ⦃ _ : discrete A ⦄ {P : A → 𝕋 ℓ} where
  enum→semiDec : Enumℙ P → ∀ x → SemiDec (P x)
  enum→semiDec e x = f , Hf where
    open Enumℙ e
    f = λ n → isSome (enumℙ n [ x ]⁻¹?)
    H : Witness enumℙ x ↔ (Σ n ， f n ≡ true)
    H .⇒ (n , x∈) = n , subst (λ x → isSome x ≡ true) (some[]⁻¹-intro x∈ .snd) refl
    H .⇐ (n , isS) with enumℙ n [ x ]⁻¹? in eq
    ... | some m = n , some[]⁻¹-elim m eq
    Hf : P x ↔ satisfied f
    Hf .⇒ = 𝟙.map (H .⇒) ∘ witℙ x .⇒
    Hf .⇐ = witℙ x .⇐ ∘ 𝟙.map (H .⇐)
```

## 马尔可夫原理

```agda
𝗠𝗣 : 𝕋
𝗠𝗣 = ∀ f → stable (satisfied f)
```

**<u>引理</u>** 假设马尔可夫原理, 离散可枚举的性质是稳定的.  

```agda
module _ ⦃ _ : discrete A ⦄ {P : A → 𝕋 ℓ} where
  𝗠𝗣→enum→stability : 𝗠𝗣 → Enumℙ P → ∀ x → stable (P x)
  𝗠𝗣→enum→stability mp e x ¬¬Px with enum→semiDec e x
  ... | f , Hf = Hf .⇐ $ mp f λ ¬sat → ¬¬Px λ Px → ¬sat $ Hf .⇒ Px
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/ReverseMaths.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.ReverseMaths.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.reverse)  
> 交流Q群: 893531731
