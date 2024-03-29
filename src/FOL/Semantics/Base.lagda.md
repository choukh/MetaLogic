---
url: fol.semantics.base
---

# 一阶逻辑 ▸ 语义 ▸ 语义蕴含

之前我们介绍了一阶逻辑的函数符号, 关系符号和变元等, 它们都是抽象符号, 没有具体所指. 在本篇中, 我们将对它们进行解释, 以赋予一阶逻辑语义. 与前面讲的语法类似, 本篇的所有内容都是以语言 `ℒ` 为参数的. 同时, 我们用 `ℒ` 实例化了前一篇提到的语法, 并将其引入.

```agda
open import Foundation.Essential
open import Foundation.ReverseMaths

open import FOL.Language.Base
module FOL.Semantics.Base (ℒ : Language) where
open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
instance _ = ℒ
```

## 解释

为了给出函数符号和关系符号的解释, 首先需要确定一个论域 (`D : 𝕋 ℓ`), 它包含了变元将要指代的那些数学对象.

**<u>定义</u>** 全体变元 `ℕ` 到论域 `D` 的映射 `ℕ → D` 叫做变元赋值表 (`Assignment`).

```agda
Assignment : (D : 𝕋 ℓ) → 𝕋 _
Assignment D = ℕ → D
```

**<u>定义</u>** 给定论域 `D`, 到其之上的符号解释 (`Interpretation`) 是一个三元组

1. 函数符号解释 `fᴵ`, 它将函数符号映射到论域上的函数
2. 关系符号解释 `Rᴵ`, 它将关系符号映射到论域上的命题性关系
3. 公式 `⊥̇` 的解释 `⊥ᴵ`, 它是一个**命题**

```agda
record Interpretation (D : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  infix 10 _⊨ₜ_ _⊨ₜ⃗_
  infix 4 _⊨ᵩ_ _⊨͆ᵩ_ _⊫ᵩ_

  field
    fᴵ : (f : 𝓕) → 𝕍 D ∣ f ∣ᶠ → D
    Rᴵ : (R : 𝓡) → 𝕍 D ∣ R ∣ᴿ → ℙ ℓ
    ⊥ᴵ : ℙ ℓ
```

**<u>注意</u>** 解释的定义中的几点注意事项

- n元函数和n元关系的n个参数统一通过n维向量传入.
- 所谓命题性关系, 是指取值到命题宇宙 `ℙ ℓ` 的关系.
- **命题** `⊥ᴵ` 用于精细控制逻辑符号 `⊥̇` 的解释, 后文中会用到.

给定一个解释, 函数和关系的意义就确定下来了. 继续给定赋值表, 配合函数符号的解释 `fᴵ`, 所有项的取值也会固定下来. 项 `t` 在赋值表 `𝓋` 下的取值, 记作 `𝓋 ⊨ₜ t`, 是论域中的一个对象; 而项的向量 `t⃗` 的取值, 记作 `𝓋 ⊨ₜ⃗ t⃗`, 是由论域中对象组成的一个向量. 与项的替换类似地, 这两者也需要互递归定义.

```agda
  _⊨ₜ_ : Assignment D → Term → D
  _⊨ₜ⃗_ : ∀ {n} → Assignment D → 𝕍 Term n → 𝕍 D n
```

**<u>互递归定义</u>** 项 `t` 在赋值表 `𝓋` 下的取值

- 单个项的取值 `𝓋 ⊨ₜ t`
  - 如果 `t` = `# n`, 则直接按赋值表 `𝓋` 赋值为 `𝓋 n`.
  - 如果 `t` = `f $̇ t⃗`, 则使用函数符号的解释得到论域上的函数 `fᴵ f`, 再应用于 `𝓋 ⊨ₜ⃗ t⃗`.
- 项的向量的取值 `𝓋 ⊨ₜ⃗ t⃗`
  - 如果 `t⃗` = `[]`, 则取值为 `[]`.
  - 如果 `t⃗` = `t ∷ t⃗`, 则取值为 `𝓋 ⊨ₜ t ∷ 𝓋 ⊨ₜ⃗ t⃗`.

```agda
  𝓋 ⊨ₜ # n = 𝓋 n
  𝓋 ⊨ₜ f $̇ t⃗ = fᴵ f (𝓋 ⊨ₜ⃗ t⃗)

  𝓋 ⊨ₜ⃗ [] = []
  𝓋 ⊨ₜ⃗ (t ∷ t⃗) = 𝓋 ⊨ₜ t ∷ 𝓋 ⊨ₜ⃗ t⃗
```

与项的替换类似地, 我们可以用列表的高阶函数 `map⃗` 把项的向量的取值 `𝓋 ⊨ₜ⃗ t⃗` 表示为 `map⃗ (𝓋 ⊨ₜ_) t⃗`.

```agda
  ⊨ₜ⃗≡map⃗ : ∀ 𝓋 {n} (t⃗ : 𝕍 Term n) → 𝓋 ⊨ₜ⃗ t⃗ ≡ map⃗ (𝓋 ⊨ₜ_) t⃗
  ⊨ₜ⃗≡map⃗ 𝓋 [] = refl
  ⊨ₜ⃗≡map⃗ 𝓋 (x ∷ t⃗) = cong (_ ∷_) $ ⊨ₜ⃗≡map⃗ 𝓋 t⃗
```

类似地, 配合关系符号的解释 `Rᴵ`, 我们可以进一步确定公式的取值 `𝓋 ⊨ᵩ φ`. 我们说 `φ` 在 `𝓋` 下**有效 (valid)** (当 `𝓋` 明确时, 简称 `φ` 有效), 当且仅当 `𝓋 ⊨ᵩ φ` 成立.

**<u>递归定义</u>** 公式 `φ` 在赋值表 `𝓋` 下的取值

- 如果 `φ` = `⊥̇`, 则取值为 `⊥ᴵ holds`.
- 如果 `φ` = `φ →̇ ψ`, 则取值为 `𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ`.
- 如果 `φ` = `∀̇ φ`, 则取值为 `(x : D) → (x ∷ₙ 𝓋) ⊨ᵩ φ`, 因为 `# 0` 是全称量词的绑定变元, 它可以换成论域中的任意对象 `x`.
- 如果 `φ` = `R $̇ t⃗`, 则使用关系符号的解释得到论域上的关系 `Rᴵ R`, 再应用于 `map⃗ (𝓋 ⊨ₜ_) t⃗`.

```agda
  _⊨ᵩ_ : Assignment D → Formula → 𝕋 _
  𝓋 ⊨ᵩ ⊥̇ = ⊥ᴵ holds
  𝓋 ⊨ᵩ φ →̇ ψ = 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ
  𝓋 ⊨ᵩ ∀̇ φ = (x : D) → (x ∷ₙ 𝓋) ⊨ᵩ φ
  𝓋 ⊨ᵩ R $̇ t⃗ = Rᴵ R (map⃗ (𝓋 ⊨ₜ_) t⃗) holds
```

**<u>引理</u>** 对任意 `𝓋` 和 `φ`, `𝓋 ⊨ᵩ φ` 是一个命题.  
**<u>证明</u>** 对公式的结构归纳, 由上面的定义, 分四种情况. 对于第一和第四种情况, 因为 `_holds` 是谓词, 所以是命题. 而第二和第三种分别是函数类型和Π类型, 其命题性都依赖于 `→` 的右边的类型的命题性, 而这只需递归使用本定理 (使用归纳假设) 即得. ∎

```agda
  isProp⊨ᵩ : ∀ 𝓋 φ → isProp (𝓋 ⊨ᵩ φ)
  isProp⊨ᵩ 𝓋 ⊥̇        = isPredHolds ⊥ᴵ
  isProp⊨ᵩ 𝓋 (φ →̇ ψ)  = isProp→ $ isProp⊨ᵩ 𝓋 ψ
  isProp⊨ᵩ 𝓋 (∀̇ φ)    = isPropΠ λ x → isProp⊨ᵩ (x ∷ₙ 𝓋) φ
  isProp⊨ᵩ 𝓋 (R $̇ t⃗)  = isPredHolds $ Rᴵ R (map⃗ (𝓋 ⊨ₜ_) t⃗)
```

**<u>定义</u>** 语境和理论的有效性

- 我们说语境 `Γ` 在 `𝓋` 下有效, 记作 `𝓋 ⊨͆ᵩ Γ`, 当且仅当 `𝓋 ⊨ᵩ φ` 对任意 `φ ∈͆ Γ` 成立.
- 我们说理论 `𝒯` 在 `𝓋` 下有效, 记作 `𝓋 ⊫ᵩ 𝒯`, 当且仅当 `𝓋 ⊨ᵩ φ` 对任意 `φ ∈ 𝒯` 成立.

```agda
  _⊨͆ᵩ_ : Assignment D → Context → 𝕋 _
  𝓋 ⊨͆ᵩ Γ = ∀ φ → φ ∈͆ Γ → 𝓋 ⊨ᵩ φ

  _⊫ᵩ_ : Assignment D → Theory → 𝕋 _
  𝓋 ⊫ᵩ 𝒯 = ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ
```

**<u>注意</u>** 以上定义的 `_⊨ₜ_ _⊨ₜ⃗_ _⊨ᵩ_ _⊨͆ᵩ_ _⊫ᵩ_` 这六个概念都是以解释为参数的.

**<u>约定</u>** 我们一次只会谈论一种解释, 它在上下文中是明确的, 首次出现时会放在括号 `⦃ ⦄` 中或使用 `instance` 关键字来声明, 所以每次提到这些概念时不会一一带上某解释 `ℐ` 作为参数, 从而精简表达. 该约定表达为以下代码.

```agda
open Interpretation ⦃...⦄ public
```

## 解释的变体

前面我们只说了 `⊥̇` 应该解释到 `⊥ᴵ holds`, 而 `⊥ᴵ` 是什么则需要进一步的解释, 这将引出解释的变体.

**<u>定义</u>** 满足某种约束 `𝒞` 的解释构成了解释的一种变体 (`Variant`), 称为 `𝒞` 变体, 记作 `𝒞 : Variant ℓ`.

```agda
Variant : ∀ ℓ → 𝕋 _
Variant ℓ = {Domain : 𝕋 ℓ} → ⦃ Interpretation Domain ⦄ → 𝕋 ℓ

private variable
  𝒞 : Variant ℓ
```

**<u>注意</u>** 关于变体的定义的两点注意事项

- 变体所带的宇宙层级参数 `ℓ` 是论域的宇宙层级.
- 定义中说的“变体”和“约束”几乎是同义词.
  - 满足约束 `𝒞` 的解释属于 `𝒞` 变体.
  - “`𝒞`” 来自“约束” (constraint) 的首字母, 而 `𝒞` 所具有的类型命名为“变体” (`Variant`).

**<u>定义</u>** 我们说变体 `𝒞₁` 包含于变体 `𝒞₂`, 当且仅当约束 `𝒞₁` 蕴含约束 `𝒞₂`.

```agda
_⊑_ : Variant ℓ → Variant ℓ → 𝕋 _
𝒞₁ ⊑ 𝒞₂ = ∀ {D} ⦃ _ : Interpretation D ⦄ → 𝒞₁ → 𝒞₂
```

**<u>定义</u>** 常用变体

- 经典变体: 使得排中律 (`((φ →̇ ψ) →̇ φ) →̇ φ`) 有效的解释
- 标准⊥变体: 把 `⊥̇` 解释为 `⊥` 的解释
- 爆炸⊥变体: 使得范围限定到关系应用的弱爆炸律 (`⊥̇ →̇ R $̇ t⃗`) 有效的解释
- 标准变体: 经典变体和标准⊥变体的交
- 爆炸变体: 经典变体和爆炸⊥变体的交

```agda
Classical Standard⊥ Exploding⊥ Std Exp : Variant ℓ
Classical   = ∀ 𝓋 φ ψ → 𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ
Standard⊥   = ⊥ᴵ holds → ⊥
Exploding⊥  = ∀ 𝓋 R t⃗ → 𝓋 ⊨ᵩ ⊥̇ →̇ R $̇ t⃗
Std         = Classical ∧ Standard⊥
Exp         = Classical ∧ Exploding⊥
```

**<u>引理</u>** 标准变体包含于爆炸变体.  
**<u>证明</u>** 显然, 将 `⊥̇` 解释为 `⊥` 会使得爆炸律有效. ∎

```agda
Standard⊥⊑Exploding⊥ : Standard⊥ {ℓ} ⊑ Exploding⊥
Standard⊥⊑Exploding⊥ std⊥ = λ _ _ _ → exfalso ∘ std⊥

Std⊑Exp : Std {ℓ} ⊑ Exp
Std⊑Exp (cls , std⊥) = cls , Standard⊥⊑Exploding⊥ std⊥
```

**<u>引理</u>** 语义爆炸律:
在爆炸⊥变体解释下, 使得恒假式 `⊥̇` 有效的任意赋值 `𝓋` 会使得任意公式 `φ` 有效.

**<u>证明</u>** 对公式的结构归纳.

- 当公式是恒假式 `⊥̇` 时, 显然成立.
- 当公式是关系应用 `R $̇ t⃗` 时, 由爆炸⊥变体的定义, 显然成立.
- 当公式是蕴含 `φ →̇ ψ` 时, 由归纳假设, 成立.
- 当公式是全称量词 `∀̇ φ` 时, 由归纳假设, 成立. ∎

```agda
semanticExplosion : ⦃ _ : Interpretation D ⦄ → Exploding⊥ →
  ∀ 𝓋 φ → 𝓋 ⊨ᵩ ⊥̇ → 𝓋 ⊨ᵩ φ
semanticExplosion exp 𝓋 ⊥̇ bot = bot
semanticExplosion exp 𝓋 (R $̇ t⃗) bot = exp 𝓋 R t⃗ bot
semanticExplosion exp 𝓋 (φ →̇ ψ) bot _ = semanticExplosion exp 𝓋 ψ bot
semanticExplosion exp 𝓋 (∀̇ φ) bot x = semanticExplosion exp (x ∷ₙ 𝓋) φ bot
```

## 语义蕴含

**<u>定义</u>** `𝒞`-语义蕴含

- 我们说语境 `Γ` 在层级 `ℓ` 中 `𝒞`-语义蕴含公式 `φ` (也说 `φ` 在 `Γ` 下 `𝒞`-有效), 记作 `Γ ⊨⟨ 𝒞 ⟩ φ` (其中 `𝒞 : Variant ℓ`), 当且仅当对解释到 `ℓ` 中论域 `D` 的任意 `𝒞` 变体 `ℐ` 都有: 任意使得 `Γ` 有效的 `𝓋` 都使得 `φ` 有效.
- 我们说理论 `𝒯` 在层级 `ℓ` 中 `𝒞`-语义蕴含公式 `φ` (也说 `φ` 在 `𝒯` 下 `𝒞`-有效), 记作 `Γ ⊫⟨ 𝒞 ⟩ φ` (其中 `𝒞 : Variant ℓ`), 当且仅当对解释到 `ℓ` 中论域 `D` 的任意 `𝒞` 变体 `ℐ` 都有: 任意使得 `𝒯` 有效的 `𝓋` 都使得 `φ` 有效.

```agda
infix 4 _⊨⟨_⟩_ _⊫⟨_⟩_

_⊨⟨_⟩_ : Context → Variant ℓ → Formula → 𝕋 _
Γ ⊨⟨ 𝒞 ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → 𝒞 → ∀ 𝓋 → 𝓋 ⊨͆ᵩ Γ → 𝓋 ⊨ᵩ φ

_⊫⟨_⟩_ : Theory → Variant ℓ → Formula → 𝕋 _
𝒯 ⊫⟨ 𝒞 ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → 𝒞 → ∀ 𝓋 → 𝓋 ⊫ᵩ 𝒯 → 𝓋 ⊨ᵩ φ
```

**<u>定义</u>** 标准-语义蕴含

- 我们说语境 `Γ` 语义蕴含 `φ` (也说 `Γ` 下 `φ` 有效), 记作 `Γ ⊨ φ`, 当且仅当对给定的宇宙层级 `ℓ` 有 `Γ ⊨⟨ Std {ℓ} ⟩ φ`.
- 我们说理论 `𝒯` 语义蕴含 `φ` (也说 `𝒯` 下 `φ` 有效), 记作 `𝒯 ⊫ φ`, 当且仅当对给定的宇宙层级 `ℓ` 有 `𝒯 ⊫⟨ Std {ℓ} ⟩ φ`.

```agda
module PolymorphicSemantics ℓ where
  infix 4 _⊨_ _⊫_

  _⊨_ : Context → Formula → 𝕋 _
  Γ ⊨ φ = Γ ⊨⟨ Std {ℓ} ⟩ φ

  _⊫_ : Theory → Formula → 𝕋 _
  𝒯 ⊫ φ = 𝒯 ⊫⟨ Std {ℓ} ⟩ φ
```

**<u>注意</u>** 语义蕴含 (semantic consequence) `_⊨_` 和上一讲的语法蕴含 (syntactic consequence) `_⊢_` 从两个不同的角度刻画了逻辑推理. 此外, 对象语言中的 `_→̇_` 又叫做实质蕴含 (material implication), 我们还有元语言蕴含 `→`, 注意区分这四种蕴含.

**<u>事实</u>** 语义蕴含是命题.  
**<u>证明</u>** 由 `isProp⊨ᵩ` 显然成立. ∎

```agda
  isProp⊨ isProp⊫ : ∀ Γ φ → isProp (Γ ⊨⟨ 𝒞 ⟩ φ)
  isProp⊨ Γ φ = isPropΠ̅ λ _ → isPropΠ̿ λ 𝒱 → isProp→ $ isPropΠ2 λ 𝓋 _ →
    let instance _ = 𝒱 in isProp⊨ᵩ 𝓋 φ
  isProp⊫ 𝒯 φ = isPropΠ̅ λ _ → isPropΠ̿ λ 𝒱 → isProp→ $ isPropΠ2 λ 𝓋 _ →
    let instance _ = 𝒱 in isProp⊨ᵩ 𝓋 φ
```

**<u>引理</u>** 语境版语义蕴含与理论版语义蕴含的互换.

```agda
⊨↔⊫ : Γ ⊨⟨ 𝒞 ⟩ φ ↔ set Γ ⊫⟨ 𝒞 ⟩ φ
⊨↔⊫ .⇒ H c 𝓋 𝓋⊫Γ = H c 𝓋 λ φ φ∈Γ → 𝓋⊫Γ φ ∣ φ∈Γ ∣₁
⊨↔⊫ .⇐ H c 𝓋 𝓋⊨Γ = H c 𝓋 λ φ φ∈Γ → 𝟙.rec (isProp⊨ᵩ 𝓋 φ) (𝓋⊨Γ φ) φ∈Γ
```

**<u>引理</u>** 语义版的语境弱化.

```agda
Wkn⊨ : ∀ φ → Γ ⊆͆ Δ → Γ ⊨⟨ 𝒞 ⟩ φ → Δ ⊨⟨ 𝒞 ⟩ φ
Wkn⊨ _ sub H c 𝓋 𝓋⊨Δ = H c 𝓋 λ ψ ψ∈Γ → 𝓋⊨Δ ψ $ sub ψ∈Γ
```

**<u>引理</u>** 语义稳定性: 标准 `𝒞`-语义蕴含是稳定的.  
**<u>证明</u>** 我们工作在经典-标准⊥语义下, 有前提 `¬ ¬ (𝒯 ⊫⟨ 𝒞 ⟩ φ)`, 且 `𝒯 ⊫ᵩ 𝓋`, 要证 `𝓋 ⊨ᵩ φ`. 由经典语义的特性, 只要证 `¬ 𝓋 ⊨ᵩ φ →̇ ⊥̇`. 假设 `𝓋 ⊨ᵩ φ →̇ ⊥̇`, 我们证 `¬ (𝒯 ⊫⟨ 𝒞 ⟩ φ)`. 假设 `𝒯 ⊫⟨ 𝒞 ⟩ φ`, 有 `𝓋 ⊨ᵩ φ`, 与 `𝓋 ⊨ᵩ φ →̇ ⊥̇` 矛盾 (因为由标准⊥语义, `𝓋 ⊨ᵩ ⊥̇` 意味着 `⊥`). ∎

```agda
semanticStability : 𝒞 ⊑ Std → stable (𝒯 ⊫⟨ 𝒞 ⟩ φ)
semanticStability {φ} sub ne c 𝓋 𝓋⊨𝒯 = let (cls , ⊥ᴵ→⊥) = sub c in
  cls 𝓋 φ ⊥̇ λ φ→⊥ᴵ → exfalso $ ne λ 𝒯⊨φ → ⊥ᴵ→⊥ $ φ→⊥ᴵ $ 𝒯⊨φ c 𝓋 𝓋⊨𝒯
```

### 语境内化的有效性

**<u>引理</u>** 如果空语境下 `φ` 有效, 那么空语境下 `φ` 的最大全称量化有效.  
**<u>证明</u>** 对全称量化的次数归纳即得. ∎

```agda
validateClose : ∀ φ → [] ⊨⟨ 𝒞 ⟩ φ → [] ⊨⟨ 𝒞 ⟩ ∀̇⋯ φ
validateClose {𝒞} φ = aux (Σfreshᵩ φ .fst) where
  aux : ∀ n → [] ⊨⟨ 𝒞 ⟩ φ → [] ⊨⟨ 𝒞 ⟩ ∀̇ⁿ n φ
  aux zero = id
  aux (suc n) H c 𝓋 _ x = aux n H c (x ∷ₙ 𝓋) λ _ ()
```

**<u>引理</u>** 如果语境 `Γ ʳ++ Δ` 下 `φ` 有效, 那么语境 `Δ` 下 `Γ ⇢ φ` 有效.  
**<u>证明</u>** 对语境 `Γ` 的长度归纳即得. ∎

```agda
validateBigImp : ∀ Γ → Γ ʳ++ Δ ⊨⟨ 𝒞 ⟩ φ → Δ ⊨⟨ 𝒞 ⟩ Γ ⇢ φ
validateBigImp [] = id
validateBigImp {Δ} {𝒞} {φ} (ψ ∷ Γ) H c 𝓋 𝓋⊫Δ 𝓋⊨ψ = validateBigImp Γ H1 c 𝓋 H2
  where
  H1 : Γ ʳ++ (ψ ∷ Δ) ⊨⟨ 𝒞 ⟩ φ
  H1 = subst (_⊨⟨ _ ⟩ φ) (sym $ ++-ʳ++ [ ψ ] {ys = Γ}) H
  H2 : 𝓋 ⊨͆ᵩ ψ ∷ Δ
  H2 φ (here refl) = 𝓋⊨ψ
  H2 φ (there φ∈Δ) = 𝓋⊫Δ φ φ∈Δ
```

**<u>引理</u>** 如果语境 `Γ` 下 `φ` 有效, 那么空语境下 `Γ ⇢ φ` 的最大全称量化有效.  
**<u>证明</u>** 由上述两条引理即得. ∎

```agda
validateInternalization : Γ ⊨⟨ 𝒞 ⟩ φ → [] ⊨⟨ 𝒞 ⟩ ∀̇⋯ (Γ ⇢ φ)
validateInternalization {Γ} {φ} H = validateClose (Γ ⇢ φ) $ validateBigImp Γ $ Wkn⊨ φ sub H where
  sub : Γ ⊆͆ Γ ʳ++ []
  sub = subst (_ ⊆͆_) (ʳ++[] Γ) ⊆reverse
```

## 结构与模型

**<u>定义</u>** 一个结构 (`Structure`) 是一个三元组

1. 论域 `Domain`
2. 到论域的符号解释 `ℐ`
3. 到论域的变元赋值表 `𝓋`

```agda
record Structure ℓ : 𝕋 (ℓ ⁺) where
  field
    { Domain } : 𝕋 ℓ
    ⦃ ℐ ⦄ : Interpretation Domain
    𝓋 : Assignment Domain
```

**<u>定义</u>** 我们说结构 `ℳ` 是理论 `𝒯` 的一个 `𝒞` 模型, 记作 `ℳ isA 𝒞 modelOf 𝒯`, 当且仅当 `ℳ` 中的解释 `ℐ` 是一个 `𝒞` 变体, 且 `ℳ` 中的赋值 `𝓋` 使得任意 `φ ∈ 𝒯` 有效.

```agda
_isA_modelOf_ : Structure ℓ → Variant ℓ → Theory → 𝕋 _
ℳ isA 𝒞 modelOf 𝒯 = 𝒞 ∧ ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ
  where open Structure ℳ
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Semantics/Base.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Semantics.Base.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.semantics.base)  
> 交流Q群: 893531731
