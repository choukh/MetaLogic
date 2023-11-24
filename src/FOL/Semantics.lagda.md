---
url: fol.semantics
---

# 一阶逻辑: 语义

之前我们介绍了一阶逻辑的函数符号, 关系符号和变量等, 它们都是抽象符号, 没有具体所指. 在本篇中, 我们将对它们进行解释, 以赋予一阶逻辑语义. 与前面讲的语法类似, 本篇的所有内容都是以语言 `ℒ` 为参数的. 同时, 我们用 `ℒ` 实例化了前一篇提到的语法, 并将其引入.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Semantics (ℒ : Language) where

open Language ℒ
open import FOL.Syntax ℒ
```

## 解释

为了给出函数符号和关系符号的解释, 首先需要确定一个论域 (`D : 𝕋 ℓ`), 它包含了变量将要指代的那些数学对象.

**<u>定义</u>** 全体变量 `ℕ` 到论域 `D` 的映射 `ℕ → D` 叫做变量赋值表 (`Valuation`).

```agda
Valuation : (D : 𝕋 ℓ) → 𝕋 _
Valuation D = ℕ → D
```

**<u>定义</u>** 给定论域 `D`, 到其之上的符号解释 (`Interpretation`) 是一个三元组

- 函数映射 `fᴵ`, 它将函数符号映射到论域上的函数
- 关系映射 `Rᴵ`, 它将关系符号映射到论域上的命题性关系
- 一个**命题** `⊥ᴵ : ℙ ℓ`

```agda
record Interpretation (D : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  infix 10 _⊨ₜ_ _⊨ₜ⃗_ _⊨ᵩ_ _⊨̌_ _⊫̌_

  field
    fᴵ : (f : 𝓕) → 𝕍 D ∣ f ∣ᶠ → D
    Rᴵ : (R : 𝓡) → 𝕍 D ∣ R ∣ᴿ → ℙ ℓ
    ⊥ᴵ : ℙ ℓ
```

**<u>注意</u>** 解释的定义中的几点注意事项

- n元函数和n元关系的n个参数统一通过n维向量传入
- 所谓命题性关系, 是指取值到命题宇宙 `ℙ ℓ` 的关系
- **命题** `⊥ᴵ` 用于精细控制逻辑符号 `⊥̇` 的解释, 后文中会用到

给定一个解释, 函数和关系的意义就确定下来了. 给定赋值表, 配合函数符号的解释 `fᴵ`, 所有项的取值也会固定下来. 项 `t` 在赋值表 `𝓋` 下的取值, 记作 `𝓋 ⊨ₜ t`, 是论域中的一个对象; 而项的向量 `t⃗` 的取值, 记作 `𝓋 ⊨ₜ⃗ t⃗`, 是由论域中对象组成的一个向量. 与项的替换类似地, 这两者也需要互递归定义.

```agda
  _⊨ₜ_ : Valuation D → Term → D
  _⊨ₜ⃗_ : ∀ {n} → Valuation D → 𝕍 Term n → 𝕍 D n
```

**<u>互递归定义</u>** 项 `t` 在赋值表 `𝓋` 下的取值

- 单个项的取值 `𝓋 ⊨ₜ t`
  - 如果 `t` = `# n`, 则直接按赋值表 `𝓋` 赋值为 `𝓋 n`
  - 如果 `t` = `f $̇ t⃗`, 则使用函数符号的解释得到论域上的函数 `fᴵ f`, 再应用于 `𝓋 ⊨ₜ⃗ t⃗`
- 项的向量的取值 `𝓋 ⊨ₜ⃗ t⃗`
  - 如果 `t⃗` = `[]`, 则取值为 `[]`
  - 如果 `t⃗` = `t ∷ t⃗`, 则取值为 `𝓋 ⊨ₜ t ∷ 𝓋 ⊨ₜ⃗ t⃗`

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

类似地, 配合关系符号的解释 `Rᴵ`, 我们可以进一步确定公式的取值 `𝓋 ⊨ᵩ φ`.

**<u>递归定义</u>** 公式 `φ` 在赋值表 `𝓋` 下的取值

- 如果 `φ` = `⊥̇`, 则取值为 `⊥ᴵ holds`
- 如果 `φ` = `φ →̇ ψ`, 则取值为 `𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ`
- 如果 `φ` = `∀̇ φ`, 则取值为 `(x : D) → (x ∷ₙ 𝓋) ⊨ᵩ φ`, 因为 `# 0` 是全称量词的绑定变量, 它可以换成论域中的任意对象 `x`
- 如果 `φ` = `R $̇ t⃗`, 则使用关系符号的解释得到论域上的关系 `Rᴵ R`, 再应用于 `map⃗ (𝓋 ⊨ₜ_) t⃗`

```agda
  _⊨ᵩ_ : Valuation D → Formula → 𝕋 _
  𝓋 ⊨ᵩ ⊥̇ = ⊥ᴵ holds
  𝓋 ⊨ᵩ φ →̇ ψ = 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ
  𝓋 ⊨ᵩ ∀̇ φ = (x : D) → (x ∷ₙ 𝓋) ⊨ᵩ φ
  𝓋 ⊨ᵩ R $̇ t⃗ = Rᴵ R (map⃗ (𝓋 ⊨ₜ_) t⃗) holds
```

**<u>定理</u>** 对任意 `𝓋` 和 `φ`, `𝓋 ⊨ᵩ φ` 是一个命题.
**<u>证明</u>** 由上面的定义, 分四种情况. 对于第一和第四种情况, 因为 `_holds` 是谓词, 所以是命题. 而第二和第三种分别是函数类型和Π类型, 其命题性都依赖于 `→` 的右边的类型的命题性, 而这只需递归调用该定理 (使用归纳假设) 即得. ∎

```agda
  isProp⊨ᵩ : ∀ 𝓋 φ → isProp (𝓋 ⊨ᵩ φ)
  isProp⊨ᵩ 𝓋 ⊥̇ = isPredHolds ⊥ᴵ
  isProp⊨ᵩ 𝓋 (φ →̇ ψ) = isProp→ $ isProp⊨ᵩ 𝓋 ψ
  isProp⊨ᵩ 𝓋 (∀̇ φ) = isPropΠ λ x → isProp⊨ᵩ (x ∷ₙ 𝓋) φ
  isProp⊨ᵩ 𝓋 (R $̇ t⃗) = isPredHolds (Rᴵ R (map⃗ (𝓋 ⊨ₜ_) t⃗))
```

**<u>定义</u>** 我们说语境 `Γ` 在 `𝓋` 下有效, 记作 `𝓋 ⊨ Γ`, 当且仅当 `𝓋 ⊨ᵩ φ` 对任意 `φ ∈ᴸ Γ` 成立.

```agda
  _⊨̌_ : Valuation D → Context → 𝕋 _
  𝓋 ⊨̌ Γ = ∀ φ → φ ∈ᴸ Γ → 𝓋 ⊨ᵩ φ
```

**<u>定义</u>** 我们说理论 `𝒯` 在 `𝓋` 下有效, 记作 `𝓋 ⊫ 𝒯`, 当且仅当 `𝓋 ⊨ᵩ φ` 对任意 `φ ∈ 𝒯` 成立.

```agda
  _⊫̌_ : Valuation D → Theory → 𝕋 _
  𝓋 ⊫̌ 𝒯 = ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ
```

## 解释的变体

上一小节我们留了一个抓手 `⊥ᴵ`, 接下来将说明它的用法.

```agda
open Interpretation ⦃...⦄ public

Variant : ∀ ℓ → 𝕋 _
Variant ℓ = {D : 𝕋 ℓ} → ⦃ Interpretation D ⦄ → 𝕋 ℓ

_⊑_ : Variant ℓ → Variant ℓ → 𝕋 _
𝒞₁ ⊑ 𝒞₂ = ∀ {D} ⦃ _ : Interpretation D ⦄ → 𝒞₁ → 𝒞₂

Classical : Variant ℓ
Classical = ∀ 𝓋 φ ψ → 𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ

Standard⊥ᴵ : Variant ℓ
Standard⊥ᴵ = ⊥ᴵ holds → ⊥

Exploding⊥ᴵ : Variant ℓ
Exploding⊥ᴵ = ∀ 𝓋 R t⃗ → 𝓋 ⊨ᵩ ⊥̇ →̇ R $̇ t⃗

Std : Variant ℓ
Std = Classical ∧ Standard⊥ᴵ

Exp : Variant ℓ
Exp = Classical ∧ Exploding⊥ᴵ

Std⊑Exp : Std {ℓ} ⊑ Exp
Std⊑Exp (cls , std⊥) = cls , λ _ _ _ → exfalso ∘ std⊥
```

## 语义蕴含

```agda
_⊨⟨_⟩_ : Context → Variant ℓ → Formula → 𝕋 _
Γ ⊨⟨ 𝒞 ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → 𝒞 → ∀ 𝓋 → 𝓋 ⊨̌ Γ → 𝓋 ⊨ᵩ φ

_⊫⟨_⟩_ : Theory → Variant ℓ → Formula → 𝕋 _
𝒯 ⊫⟨ 𝒞 ⟩ φ = ∀ {D} ⦃ _ : Interpretation D ⦄ → 𝒞 → ∀ 𝓋 → 𝓋 ⊫̌ 𝒯 → 𝓋 ⊨ᵩ φ
```

**<u>定理</u>** 语义蕴含是命题.
**<u>证明</u>** 由 `isProp⊨ᵩ` 显然成立. ∎

```agda
isProp⊨⟨⟩ : ∀ Γ {𝒞 : Variant ℓ} φ → isProp (Γ ⊨⟨ 𝒞 ⟩ φ)
isProp⊨⟨⟩ Γ φ = isPropΠ̅ λ _ → isPropΠ̿ λ 𝒱 → isProp→ $ isPropΠ2 λ 𝓋 _ →
  let instance _ = 𝒱 in isProp⊨ᵩ 𝓋 φ

isProp⊫⟨⟩ : ∀ 𝒯 {𝒞 : Variant ℓ} φ → isProp (𝒯 ⊫⟨ 𝒞 ⟩ φ)
isProp⊫⟨⟩ 𝒯 φ = isPropΠ̅ λ _ → isPropΠ̿ λ 𝒱 → isProp→ $ isPropΠ2 λ 𝓋 _ →
  let instance _ = 𝒱 in isProp⊨ᵩ 𝓋 φ
```

**<u>注意</u>** 语义蕴含 `_⊨_` 和上一篇讲的语法蕴含 `_⊢_` 从两个不同的角度刻画了逻辑推理. 此外, 对象语言中的 `_→̇_` 又叫做实质蕴含, 我们还有元语言蕴含 `→`, 注意区分这四种蕴含.

## 结构与模型

**<u>定义</u>** 一个结构 (`Structure`) 是一个三元组

- 论域 `Domain`
- 到论域的变量赋值表 `𝓋`
- 到论域的符号解释 `ℐ`

```agda
record Structure ℓ : 𝕋 (ℓ ⁺) where
  field
    Domain : 𝕋 ℓ
    𝓋 : Valuation Domain
    ⦃ ℐ ⦄ : Interpretation Domain
```

**<u>定义</u>** 我们说 `ℳ` 是理论 `𝒯` 的一个 `𝒞` 模型, 记作 `ℳ isA 𝒞 modelOf 𝒯`, 当且仅当 `ℳ` 中的解释 `ℐ` 是一个 `𝒞` 变体解释, 且`ℳ` 中的赋值 `𝓋` 使得对任意 `φ ∈ 𝒯` 有 `𝓋 ⊨ᵩ φ` 成立.

```agda
_isA_modelOf_ : Structure ℓ → Variant ℓ → Theory → 𝕋 _
ℳ isA 𝒞 modelOf 𝒯 = 𝒞 ∧ ∀ φ → φ ∈ 𝒯 → 𝓋 ⊨ᵩ φ
  where open Structure ℳ
```
