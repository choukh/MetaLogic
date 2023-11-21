---
url: fol.syntax
---

# 一阶逻辑: 语法

本篇引入一阶逻辑的**项 (term)**和**公式 (formula)**, 它们共同构成了一阶逻辑的语法. 项由变量和函数符号构成; 公式则由关系符号和逻辑符号构成. 粗略类比, 如果说符号相当于字, 那么项和公式则相当于词和句. 注意本篇所有内容都是参数化到语言的.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax (ℒ : Language) where
open Language ℒ
```

以下列出了本篇所引入的符号的优先级. 数字越大则优先级越高, 未列出的符号默认具有 20 的优先级. 它们的具体定义会在后文给出.

```agda
infix 10 _⊢_ _⊬_ _⊩_ _⊮_
infixl 15 _→̇_
infix 30 _[_]ₜ _[_]ₜ⃗ _[_]ᵩ
```

## 项

我们采用 [De Brujin编码](https://en.wikipedia.org/wiki/De_Bruijn_index), 用自然数作变量.

**<u>定义</u>** 有且仅有以下是项:

- 对任意自然数 `n`, `# n` 是项 (变量)
- 对任意 `l` 元函数符号 `f`, `f $̇ t⃗` 是项 (函数应用), 其中 `t⃗` 是项的 `l` 维向量

```agda
data Term : 𝕋 where
  #_ : ℕ → Term
  _$̇_ : (f : 𝓕) → 𝕍 Term ∣ f ∣ᶠ → Term
```

### 项的替换

**<u>定义</u>** 项的无穷序列叫做变量替换表 (`σ : Subst`), 它记录了全体自然数 (变量) 与项的一套对应关系.

```agda
Subst : 𝕋
Subst = ℕ → Term
```

我们想要把变量替换表作用到项上, 这需要同时 (互递归) 定义单个项的替换 `t [ σ ]ₜ` 以及项的向量整体的替换 `t⃗ [ σ ]ₜ⃗`.

```agda
_[_]ₜ : Term → Subst → Term
_[_]ₜ⃗ : ∀ {n} → 𝕍 Term n → Subst → 𝕍 Term n
```

**<u>互递归定义</u>** 项的替换:

- 单个项的替换 `t [ σ ]ₜ`:
  - 如果 `t` = `# n`, 则替换后为 `σ n`
  - 如果 `t` = `f $̇ t⃗`, 则替换后为 `f $̇ t⃗ [ σ ]ₜ⃗`
- 项的向量整体的替换 `t⃗ [ σ ]ₜ⃗`:
  - 如果 `t⃗` = `[]`, 则替换后为 `[]`
  - 如果 `t⃗` = `t ∷ t⃗`, 则替换后为 `t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗`

```agda
(# n)   [ σ ]ₜ = σ n
(f $̇ t⃗) [ σ ]ₜ = f $̇ t⃗ [ σ ]ₜ⃗

[] [ σ ]ₜ⃗ = []
(t ∷ t⃗) [ σ ]ₜ⃗ = t [ σ ]ₜ ∷ t⃗ [ σ ]ₜ⃗
```

标准库中定义了向量的高阶函数 `map⃗`, 用于对向量 `x⃗` 中的每个元素做相同变换 `f`, 所得到的向量记作 `map⃗ f x⃗`. 项的向量整体的替换 `t⃗ [ σ ]ₜ⃗` 也可以用 `map⃗` 来表示, 以套用库中关于 `map⃗` 的引理.

```agda
[]ₜ⃗≡map⃗ : ∀ {n} (t⃗ : 𝕍 Term n) σ → t⃗ [ σ ]ₜ⃗ ≡ map⃗ (_[ σ ]ₜ) t⃗
[]ₜ⃗≡map⃗ [] σ = refl
[]ₜ⃗≡map⃗ (_ ∷ t⃗) σ = cong (_ ∷_) $ []ₜ⃗≡map⃗ t⃗ σ
```

### 项的提升

**<u>定义</u>** 项 `t` 的提升 `↑ₜ t` 是指对 `t` 中使用的所有变量 (自然数) 做一次后继.

```agda
↑ₜ : Term → Term
↑ₜ = _[ #_ ∘ suc ]ₜ
```

例如, 若 `t` = `g $ (f $̇ # 0) ∷ [ # 1 ]`, 那么 `↑ₜ t` = `g $ (f $̇ # 1) ∷ [ # 2 ]`.

## 公式

```agda
data Formula : 𝕋 where
  ⊥̇ : Formula
  _$̇_ : (R : 𝓡) → 𝕍 Term ∣ R ∣ᴿ → Formula
  _→̇_ : Formula → Formula → Formula
  ∀̇_ : Formula → Formula
```

### 公式的替换

```agda
_[_]ᵩ : Formula → Subst → Formula
⊥̇       [ σ ]ᵩ = ⊥̇
(R $̇ t⃗) [ σ ]ᵩ = R $̇ map⃗ (_[ σ ]ₜ) t⃗
(φ →̇ ψ) [ σ ]ᵩ = φ [ σ ]ᵩ →̇ ψ [ σ ]ᵩ
(∀̇ φ)   [ σ ]ᵩ = ∀̇ φ [ # 0 ∷ₙ ↑ₜ ∘ σ ]ᵩ
```

```agda
_[_∷] : Formula → Term → Formula
φ [ t ∷] = φ [ t ∷ₙ #_ ]ᵩ
```

### 公式的提升

```agda
↑ᵩ : Formula → Formula
↑ᵩ = _[ #_ ∘ suc ]ᵩ
```

## 语境与理论

```agda
Context : 𝕋
Context = 𝕃 Formula

Theory : 𝕋₁
Theory = 𝒫 Formula
```

### 语境的提升

```agda
↑ : Context → Context
↑ = map ↑ᵩ
```

## 证明

```agda
variable
  t : Term
  φ ψ : Formula
  Γ : Context
  𝒯 : Theory
```

```agda
data _⊢_ : Context → Formula → 𝕋 where
  Ctx     : φ ∈ᴸ Γ             → Γ ⊢ φ
  ImpI    : (φ ∷ Γ) ⊢ ψ       → Γ ⊢ φ →̇ ψ
  ImpE    : Γ ⊢ φ →̇ ψ → Γ ⊢ φ → Γ ⊢ ψ
  AllI    : ↑ Γ ⊢ φ           → Γ ⊢ ∀̇ φ
  AllE    : Γ ⊢ ∀̇ φ           → Γ ⊢ φ [ t ∷]
  FalseE  : Γ ⊢ ⊥̇             → Γ ⊢ φ
  Peirce  : ∀ φ ψ → Γ ⊢ ((φ →̇ ψ) →̇ φ) →̇ φ
```

```agda
_⊬_ : Context → Formula → 𝕋
Γ ⊬ φ = ¬ (Γ ⊢ φ)
```

```agda
_⊩_ : Theory → Formula → 𝕋
𝒯 ⊩ φ = Σ _ λ Γ → (∀ φ → φ ∈ᴸ Γ → φ ∈ 𝒯) → Γ ⊢ φ

_⊮_ : Theory → Formula → 𝕋
𝒯 ⊮ φ = ¬ (𝒯 ⊩ φ)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax)  
> 交流Q群: 893531731
