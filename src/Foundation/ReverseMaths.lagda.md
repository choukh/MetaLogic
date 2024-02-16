---
url: foundation.reverse
---

# 元语言 ▸ 构造主义反推基础

在纯构造主义中工作的好处是我们可以随时按需添加非纯构造公理 (如 𝗔𝗖, 𝗟𝗘𝗠, 𝗟𝗣𝗢, 𝗠𝗣, 以及它们的各种变体), 以调节元理论的非构造强度, 从而分析我们关心的命题的构造主义纯度. 此种实践我们称为构造主义反推数学, 而本章的目的就是介绍其基本设定.

```agda
module Foundation.ReverseMaths where

open import Foundation.Essential
open import Foundation.Relation.Nullary.Discrete.List
```

## 居留与非空

**<u>定义</u>** 居留与非空:

- 我们说类型 `A` 居留, 当且仅当存在 `a : A`.
- 我们说类型 `A` 非空, 当且仅当 `¬ ¬ A` 成立.

```agda
inhabited nonEmpty : 𝕋 ℓ → 𝕋 ℓ
inhabited A = ∥ A ∥₁
nonEmpty A = ¬ ¬ A
```

**<u>事实</u>** 居留蕴含非空.

```agda
_ : inhabited A → nonEmpty A
_ = 𝟙.rec isProp¬ λ a ¬a → ¬a a
```

**<u>事实</u>** 如果 `A` 蕴含 `B`, 那么 `A` 居留蕴含 `B` 居留.

```agda
_ : (A → B) → inhabited A → inhabited B
_ = 𝟙.map
```

**<u>引理</u>** 非空类型的替换:

- 如果 `A` 蕴含 `B`, 那么 `A` 非空蕴含 `B` 非空.
- 如果 `A` 居留蕴含 `B` 居留, 那么 `A` 非空蕴含 `B` 非空.

```agda
nonEmpty-subst : (A → B) → nonEmpty A → nonEmpty B
nonEmpty-subst ab neA ¬b = neA $ ¬b ∘ ab

nonEmpty-subst₁ : (∥ A ∥₁ → ∥ B ∥₁) → nonEmpty A → nonEmpty B
nonEmpty-subst₁ ab neA ¬b = neA λ a → 𝟙.rec isProp⊥ ¬b (ab ∣ a ∣₁)
```

**<u>引理</u>** `A` 非空等价于 `A` 的居留性非空.

```agda
nonEmptyInhabitation : nonEmpty A ↔ nonEmpty (inhabited A)
nonEmptyInhabitation .⇒ ¬¬a ¬∣a∣ = ¬¬a λ a → ¬∣a∣ ∣ a ∣₁
nonEmptyInhabitation .⇐ ¬¬∣a∣ = ¬¬∣a∣ ∘ 𝟙.rec isProp⊥
```

## 稳定性

**<u>定义</u>** 稳定性:

- 我们说类型 `A` **稳定**, 当且仅当 `A` 非空蕴含 `A`.
- 我们说类型 `A` **居留稳定**, 当且仅当 `A` 的非空性蕴含 `A` 的居留性.

```agda
stable : 𝕋 ℓ → 𝕋 ℓ
stable A = nonEmpty A → A

stable₁ : 𝕋 ℓ → 𝕋 ℓ
stable₁ A = nonEmpty A → inhabited A
```

**<u>引理</u>** 稳定类型的替换:

- 如果 `A` 与 `B` 逻辑等价, 那么 `A` 的稳定性蕴含 `B` 的稳定性.
- 如果 `A` 的居留性与 `B` 的居留性等价, 那么 `A` 的居留稳定性蕴含 `B` 的居留稳定性.

```agda
stable-subst : A ↔ B → stable A → stable B
stable-subst iff stbA = iff .⇒ ∘ stbA ∘ nonEmpty-subst (iff .⇐)

stable₁-subst : ∥ A ∥₁ ↔ ∥ B ∥₁ → stable₁ A → stable₁ B
stable₁-subst iff stbA = iff .⇒ ∘ stbA ∘ nonEmpty-subst₁ (iff .⇐)
```

**<u>引理</u>** `A` 的居留稳定性等价于 `A` 的居留性的稳定性.

```agda
stableInhabitation : stable₁ A ↔ stable (inhabited A)
stableInhabitation .⇒ stbA = stbA ∘ nonEmptyInhabitation .⇐
stableInhabitation .⇐ stbA = stbA ∘ nonEmptyInhabitation .⇒
```

## 排中律

众所周知, 排中律导向经典数学. 它有多种等价形式, 我们介绍两种. 给定宇宙层级 `ℓ`.

```agda
module _ {ℓ} where
```

**<u>定义</u>** 我们说 `ℓ` 中排中律成立, 当且仅当 `ℓ` 中的任意命题 `P` 都是可判定的.

```agda
  𝗟𝗘𝗠 : 𝕋 (ℓ ⁺)
  𝗟𝗘𝗠 = (P : 𝕋 ℓ) → isProp P → Dec P
```

**<u>引理</u>** `ℓ` 中的任意类型 `A` 的可判定性非空.

```agda
  Dec-nonEmpty : nonEmpty (Dec A)
  Dec-nonEmpty demon = demon $ no $ demon ∘ yes
```

**<u>定义</u>** 双重否定消去律:

- 形式0: `ℓ` 中的任意命题 `P` 稳定.
- 形式1: `ℓ` 中的任意类型 `A` 居留稳定.

```agda
  𝗗𝗡𝗘 : 𝕋 (ℓ ⁺)
  𝗗𝗡𝗘 = (P : 𝕋 ℓ) → isProp P → stable P

  𝗗𝗡𝗘₁ : 𝕋 (ℓ ⁺)
  𝗗𝗡𝗘₁ = (A : 𝕋 ℓ) → stable₁ A
```

**<u>事实</u>** 形式0与形式1等价.

```agda
  𝗗𝗡𝗘↔𝗗𝗡𝗘₁ : 𝗗𝗡𝗘 ↔ 𝗗𝗡𝗘₁
  𝗗𝗡𝗘↔𝗗𝗡𝗘₁ .⇒ dne A = stableInhabitation .⇐ (dne ∥ A ∥₁ 𝟙.squash)
  𝗗𝗡𝗘↔𝗗𝗡𝗘₁ .⇐ dne₁ P propP ne = 𝟙.rec propP id (dne₁ P ne)
```

**<u>定理</u>** 排中律与双重否定消去律等价.  
**<u>证明</u>**

- 左到右: 由排中律, 讨论 `P`.
  - `P` 成立: 直接就是 `𝗗𝗡𝗘` 的结论.
  - `¬ P` 成立: 由 `𝗗𝗡𝗘` 的前提, `¬ ¬ P` 成立, 矛盾.
- 右到左: 由引理 `Dec-nonEmpty`, `P` 的可判定性非空. 由 `𝗗𝗡𝗘` 即得 `P` 的可判定性. ∎

```agda
  𝗟𝗘𝗠↔𝗗𝗡𝗘 : 𝗟𝗘𝗠 ↔ 𝗗𝗡𝗘
  𝗟𝗘𝗠↔𝗗𝗡𝗘 .⇒ lem P propP with lem P propP
  ... | yes p = λ _ → p
  ... | no ¬p = λ ¬¬p → exfalso (¬¬p ¬p)
  𝗟𝗘𝗠↔𝗗𝗡𝗘 .⇐ dne P propP = dne (Dec P) (isPredDec propP) Dec-nonEmpty
```

## 半可判定

**<u>定义</u>** 我们说一串比特 (`true` | `false`) 序列 `f` 见证了真, 当且仅当存在 `n` 使得 `f n ≡ true` 成立.

```agda
truthy : (ℕ → 𝔹) → 𝕋
truthy f = ∃ n ， f n ≡ true
```

**<u>定义</u>** 我们说 `f` 是类型 `A` 半判定器, 当且仅当 `A` 逻辑等价于 `f` 见证了真.

```agda
SemiDec : 𝕋 ℓ → 𝕋 _
SemiDec A = Σ f ， A ↔ truthy f
```

**<u>引理</u>** 给定关于离散类型 `A` 的性质 `P`, `P` 的枚举算法可以转化为任意 `P x` 的半判定器. 也就是说, 离散可枚举的性质是半可判定的.  
**<u>证明</u>** 由枚举的定义, `P` 的枚举算法给了我们 `P` 的步进累积列表 `enumℙ : ℕ → 𝕃 A`, 满足对任意 `x`, `P x` 当且仅当 `enumℙ` 见证 `x`. 定义 `P x` 的半判定器为, 输入任意 `n`, 判定 `x` 是否在序列 `enumℙ n` 中 (由于 `A` 离散, 所以可以判定), 以此输出真假. ∎

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
    Hf : P x ↔ truthy f
    Hf .⇒ = 𝟙.map (H .⇒) ∘ witℙ x .⇒
    Hf .⇐ = witℙ x .⇐ ∘ 𝟙.map (H .⇐)
```

## 马尔可夫原理

马尔可夫原理导向**俄国构造主义学派 (Russian constructivism)**.

**<u>定义</u>** **马尔可夫原理 (Markov's principle)**: 任意比特序列对真的见证都是稳定的. 也就是说, 如果并非对任意 `n` 都有 `f n ≡ true` 为假, 那么存在 `n` 使得 `f n ≡ true` 为真.

```agda
𝗠𝗣 : 𝕋
𝗠𝗣 = ∀ f → stable (truthy f)
```

**<u>定理 (MP)</u>** 离散可枚举的性质是稳定的.  
**<u>证明</u>** 假设 `P x` 并非不成立, 要证 `P x` 成立. 由引理 `num→semiDec`, 我们有 `P x` 的半判定器 `f`, 满足 `P x` 成立当且仅当 `f` 见证真. 我们证 `f` 见证真. 由 `𝗠𝗣`, 只要证 `f` 并非不见证真. 假设 `f` 不见证真, 那么 `P x` 也不成立, 与 `P x` 并非不成立矛盾. ∎

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
