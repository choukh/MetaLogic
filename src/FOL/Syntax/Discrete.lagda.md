---
url: fol.syntax.discrete
---

# 一阶逻辑 ▸ 语法 ▸ 公式的离散性

我们希望说明公式类型 `Formula` 是一个集合, 并且可以被枚举. 这些都要求首先建立公式的离散性.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.Discrete (ℒ : Language) where

open import FOL.Syntax.Base ℒ
instance _ = ℒ
```

## 构造子的单射性

为了证明公式的离散性, 首先需要证明项和公式的每一个构造子都是单射, 因为我们需要从某 `x ≢ y` 说明 `f x ≢ f y`, 其中 `f` 是某个构造子. 大部分构造子的单射性都是显然的, 如下所示.

```agda
#-inj : {m n : ℕ} → # m ≡ # n → m ≡ n
#-inj refl = refl

f$̇-injˡ : ∀ {f g t⃗ s⃗} → f Term.$̇ t⃗ ≡ g $̇ s⃗ → f ≡ g
f$̇-injˡ refl = refl

→̇-injˡ : ∀ {φ₁ ψ₁ φ₂ ψ₂} → φ₁ →̇ ψ₁ ≡ φ₂ →̇ ψ₂ → φ₁ ≡ φ₂
→̇-injˡ refl = refl

→̇-injʳ : ∀ {φ₁ ψ₁ φ₂ ψ₂} → φ₁ →̇ ψ₁ ≡ φ₂ →̇ ψ₂ → ψ₁ ≡ ψ₂
→̇-injʳ refl = refl

∀̇-inj : ∀ {φ₁ φ₂} → ∀̇ φ₁ ≡ ∀̇ φ₂ → φ₁ ≡ φ₂
∀̇-inj refl = refl

R$̇-injˡ : ∀ {R S t⃗ s⃗} → R Formula.$̇ t⃗ ≡ S $̇ s⃗ → R ≡ S
R$̇-injˡ refl = refl
```

**<u>引理</u>** `f $̇_` 和 `R $̇_` 都是单射.  
**<u>证明</u>** 它们的证明思路是一样的, 我们只说前者. 首先需要把函数应用的相等 `f $̇ t⃗ ≡ f $̇ s⃗` 转化为元数和参数向量组成的依值对子的相等 `(∣ f ∣ᶠ , t⃗) ≡ (∣ f ∣ᶠ , s⃗)`. 这样就可以用依值对子类型 `Σ` 的构造子 `x ,_` 的单射性来证明配对的右边相等. 这要求配对的左边 `x` 是离散集的元素. 在本命题中, 配对的左边是元数 `∣ f ∣ᶠ`, 也即自然数, 确实是离散集. ∎

```agda
f$̇-injʳ : ∀ {f t⃗ s⃗} → f $̇ t⃗ ≡ f $̇ s⃗ → t⃗ ≡ s⃗
f$̇-injʳ {f} {t⃗} {s⃗} eq = ,-injʳ discreteSet eqΣ where
  toΣ : Term → Σ n ， 𝕍 Term n
  toΣ (# n) = 0 , []
  toΣ (f $̇ t⃗) = ∣ f ∣ᶠ , t⃗
  eqΣ : (∣ f ∣ᶠ , t⃗) ≡ (∣ f ∣ᶠ , s⃗)
  eqΣ = cong toΣ eq

R$̇-injʳ : ∀ {R t⃗ s⃗} → R $̇ t⃗ ≡ R $̇ s⃗ → t⃗ ≡ s⃗
R$̇-injʳ {R} {t⃗} {s⃗} eq = ,-injʳ discreteSet eqΣ where
  toΣ : Formula → Σ n ， 𝕍 Term n
  toΣ ⊥̇ = 0 , []
  toΣ (_ →̇ _) = 0 , []
  toΣ (∀̇ _) = 0 , []
  toΣ (R $̇ t⃗) = ∣ R ∣ᴿ , t⃗
  eqΣ : (∣ R ∣ᴿ , t⃗) ≡ (∣ R ∣ᴿ , s⃗)
  eqΣ = cong toΣ eq
```

## 项和公式的离散性

**<u>实例</u>** 项类型 `Term` 是离散集.  
**<u>证明</u>** 同时对左右两边两个项的结构归纳.

- 当一个项是变元另一个项是函数应用时判定为不相等.

- 当两个项都是变元时, 判定代表变元的那两个自然数是否相等.
  - 若相等, 则两个变元判定为相等.
  - 若不相等, 则两个变元判定为不相等. 不然的话, 由 `#` 的单射性, 两个自然数应该相等.

- 当两个项都是函数应用 `f $̇ t⃗` 时, 有归纳假设 `∀ t → t ∈⃗ t⃗ → ∀ s → Dec (t ≡ s)`. 判定两个函数符号是否相等.
  - 若不相等, 则两个变元判定为不相等. 不然的话, 由 `f$̇-injˡ`, 两个函数应用的函数符号应该相等.
  - 若相等, 继续判断参数向量组是否相等. 注意这一步使用了归纳假设.
    - 若相等, 则两个变元判定为相等.
    - 若不相等, 则两个变元判定为不相等. 不然的话, 由 `f$̇-injʳ`, 两个函数应用的参数向量组应该相等. ∎

```agda
instance
  discrTerm : discrete Term
  discrTerm = term-elim {P = λ t → ∀ s → Dec (t ≡ s)} H# H$̇ _ _ where
    H# : (m : ℕ) (s : Term) → Dec (# m ≡ s)
    H# m (# n) with m ≟ n
    ... | yes refl = yes refl
    ... | no ¬eq = no $ ¬eq ∘ #-inj
    H# m (f $̇ t⃗) = no λ ()
    H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → ∀ s → Dec (t ≡ s)) → ∀ s → Dec (f $̇ t⃗ ≡ s)
    H$̇ f t⃗ IH (# n) = no λ ()
    H$̇ f t⃗ IH (g $̇ s⃗) with f ≟ g
    ... | no ¬eq = no $ ¬eq ∘ f$̇-injˡ
    ... | yes refl with discrete𝕍-strong t⃗ s⃗ IH
    ... | yes refl = yes refl
    ... | no ¬eq = no $ ¬eq ∘ f$̇-injʳ
```

**<u>实例</u>** 公式类型 `Formula` 是离散集.  
**<u>证明</u>** 同时对左右两边两个公式的结构归纳. 如果左右两边的项使用不同的构造子构造, 则直接判定为不相等. 否则递归判定构造子所涉及的参数. 如果递归的某一步出现不相等的情况, 则用相应的构造子单射性判定原公式不相等. 否则最终判定原公式相等. ∎

```agda
  discrFormula : discrete Formula
  discrFormula = H _ _ where
    H : ∀ φ ψ → Dec (φ ≡ ψ)
    H ⊥̇ ⊥̇ = yes refl
    H ⊥̇ (_ →̇ _) = no λ ()
    H ⊥̇ (∀̇ _) = no λ ()
    H ⊥̇ (_ $̇ _) = no λ ()
    H (φ₁ →̇ ψ₁) ⊥̇ = no λ ()
    H (φ₁ →̇ ψ₁) (φ₂ →̇ ψ₂) with H φ₁ φ₂ | H ψ₁ ψ₂
    ... | yes refl | yes refl = yes refl
    ... | no ¬eq   | _        = no $ ¬eq ∘ →̇-injˡ
    ... | _        | no ¬eq   = no $ ¬eq ∘ →̇-injʳ
    H (φ₁ →̇ ψ₁) (∀̇ _) = no λ ()
    H (φ₁ →̇ ψ₁) (_ $̇ _) = no λ ()
    H (∀̇ φ) ⊥̇ = no λ ()
    H (∀̇ φ) (_ →̇ _) = no λ ()
    H (∀̇ φ) (∀̇ ψ) with H φ ψ
    ... | yes refl = yes refl
    ... | no ¬eq   = no $ ¬eq ∘ ∀̇-inj
    H (∀̇ φ) (_ $̇ _) = no λ ()
    H (R $̇ t⃗) ⊥̇ = no λ ()
    H (R $̇ t⃗) (_ →̇ _) = no λ ()
    H (R $̇ t⃗) (∀̇ _) = no λ ()
    H (R $̇ t⃗) (S $̇ s⃗) with R ≟ S
    ... | no ¬eq = no $ ¬eq ∘ R$̇-injˡ
    ... | yes refl with t⃗ ≟ s⃗
    ... | yes refl = yes refl
    ... | no ¬eq = no $ ¬eq ∘ R$̇-injʳ
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Discrete.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Discrete.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.discrete)  
> 交流Q群: 893531731
