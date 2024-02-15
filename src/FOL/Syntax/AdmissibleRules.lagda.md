---
url: fol.syntax.admissible
---

# 一阶逻辑 ▸ 语法 ▸ 可容许规则

若在一个形式系统中添加一个推理规则后, 该系统的定理集合不发生变化, 则称该推理规则在该形式系统中是**可容许的 (admissible)**. 换句话说, 使用该规则可证明的每个公式在没有该规则的情况下已经是可证明的. 因此在某种程度上说, 该规则是冗余的. 但是对于研究这个系统而言, 它们是重要引理.

```agda
open import Foundation.Essential
open import FOL.Language.Base
module FOL.Syntax.AdmissibleRules (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
open import FOL.Syntax.SubstitutionFacts ℒ

private variable
  n : ℕ
```

## 演绎记法

我们先定义以下演绎记法, 用它可以使大部分可容许规则的证明在形式上自明, 对这种我们不再给出自然语言证明.

```agda
infix 1 tautology
infixl 0 deduction

tautology : (A : 𝕋) → A → A
tautology A a = a

deduction : A → (B : 𝕋) → (A → B) → B
deduction a B ab = ab a

syntax tautology A a = ∅─⟨ a ⟩ A
syntax deduction a B ab = a ─⟨ ab ⟩ B
```

以下是两个简单的例子.

**<u>规则</u>** `Ctx` 的变体.

```agda
Ctx0 : φ ∷ Γ ⊢ φ
Ctx0 {φ} {Γ} =
             ∅─⟨ here refl ⟩
  φ ∈ᴸ φ ∷ Γ ─⟨ Ctx ⟩
  φ ∷ Γ ⊢ φ
```

**<u>规则</u>** `ImpI` 的变体.

```agda
ImpI′ : (∀ {Γ} → Γ ⊢ φ → Γ ⊢ ψ) → Γ ⊢ φ →̇ ψ
ImpI′ {φ} {ψ} {Γ} H =
            ∅─⟨ Ctx0 ⟩
  φ ∷ Γ ⊢ φ ─⟨ H ⟩
  φ ∷ Γ ⊢ ψ ─⟨ ImpI ⟩
  Γ ⊢ φ →̇ ψ
```

## 语境弱化

弱化指的是对语境的弱化. 此类规则允许我们通过在弱化的语境中证明某公式, 来说明原语境中就能证明该公式.

**<u>规则</u>** 弱化: `Γ ⊆ᴸ Δ` 蕴含 `Γ ⊢ φ → Δ ⊢ φ`.  
**<u>证明</u>** 对证明树归纳即得. ∎

```agda
Wkn : Γ ⊆ᴸ Δ → Γ ⊢ φ → Δ ⊢ φ
Wkn sub (Ctx H) = Ctx (sub H)
Wkn sub (ImpI H) = ImpI (Wkn (∷⊆∷ sub) H)
Wkn sub (ImpE H₁ H₂) = ImpE (Wkn sub H₁) (Wkn sub H₂)
Wkn sub (AllI H) = AllI (Wkn (map⊆map sub) H)
Wkn sub (AllE H) = AllE (Wkn sub H)
Wkn sub (FalseE H) = FalseE (Wkn sub H)
Wkn sub (Peirce φ ψ) = Peirce φ ψ
```

**<u>规则</u>** 替换弱化: 一个证明在其语境和结论同时做同种替换后仍然有效.  
**<u>证明</u>** 对证明树归纳. 除 `AllI` 和 `AllE` 之外的情况的证明与 `Wkn` 类似.

```agda
SubstWkn : (σ : Subst) → Γ ⊢ φ → map _[ σ ]ᵩ Γ ⊢ φ [ σ ]ᵩ
SubstWkn σ (Ctx H) = Ctx (∈map-intro H refl)
SubstWkn σ (ImpI H) = ImpI (SubstWkn σ H)
SubstWkn σ (ImpE H₁ H₂) = ImpE (SubstWkn σ H₁) (SubstWkn σ H₂)
SubstWkn σ (FalseE H) = FalseE (SubstWkn σ H)
SubstWkn σ (Peirce φ ψ) = Peirce (φ [ σ ]ᵩ) (ψ [ σ ]ᵩ)
```

对于 `AllI` 的情况, 要证 `map (_[ σ ]ᵩ) Γ ⊢ (∀̇ φ) [ σ ]ᵩ`.
有归纳假设 `map (_[ ↑ₛ σ ]ᵩ) (⇞ Γ) ⊢ φ [ ↑ₛ σ ]ᵩ`.
对目标使用 `AllI` 归纳, 只要证 `⇞ (map (_[ σ ]ᵩ) Γ) ⊢ φ [ ↑ₛ σ ]ᵩ`.
将目标 `⊢` 式的左边换成 `map (_[ ↑ₛ σ ]ᵩ) (⇞ Γ)` 即证. ∎

```agda
SubstWkn {Γ} σ (AllI H) = AllI $ subst (_⊢ _) ↑∘[] (SubstWkn (↑ₛ σ) H)
```

对于 `AllE` 的情况, 要证 `map (_[ σ ]ᵩ) Γ ⊢ (φ [ t ]₀) [ σ ]ᵩ`.
有归纳假设 `map (_[ σ ]ᵩ) Γ ⊢ (∀̇ φ) [ σ ]ᵩ`.
对归纳假设使用 `AllE` 规则, 可得对任意 `t` 有 `map (_[ σ ]ᵩ) Γ ⊢ (φ [ ↑ₛ σ ]ᵩ) [ t ]₀`.
将目标 `⊢` 式的右边可以换成 `(φ [ ↑ₛ σ ]ᵩ) [ t [ σ ]ₜ ]₀` 即证.

```agda
SubstWkn σ (AllE H) = subst (_ ⊢_) ([]ᵩ∘[]₀ _) (AllE (SubstWkn σ H))
```

**<u>规则</u>** `Wkn` 的变体.

```agda
Wkn0 : Γ ⊢ ψ → φ ∷ Γ ⊢ ψ
Wkn0 {Γ} {ψ} {φ} H =
            ∅─⟨ H ⟩
  Γ ⊢ ψ     ─⟨ Wkn sub ⟩
  φ ∷ Γ ⊢ ψ
  where
  sub : Γ ⊆ᴸ φ ∷ Γ
  sub = there
```

**<u>规则</u>** `ImpI` 的弱化: 可以通过证明蕴含式的右边可证明来证明原蕴含式.

```agda
WknImpI : Γ ⊢ ψ → Γ ⊢ φ →̇ ψ
WknImpI {Γ} {ψ} {φ} H =
            ∅─⟨ H ⟩
  Γ ⊢ ψ     ─⟨ Wkn0 ⟩
  φ ∷ Γ ⊢ ψ ─⟨ ImpI ⟩
  Γ ⊢ φ →̇ ψ
```

**<u>规则</u>** 蕴含式的应用.

```agda
App : Γ ⊢ φ → φ →̇ ψ ∷ Γ ⊢ ψ
App {Γ} {φ} {ψ} H = ImpE H₁ H₂ where
  H₁ =                ∅─⟨ Ctx0 ⟩
    φ →̇ ψ ∷ Γ ⊢ φ →̇ ψ
  H₂ =                ∅─⟨ H ⟩
    Γ ⊢ φ             ─⟨ Wkn0 ⟩
    φ →̇ ψ ∷ Γ ⊢ φ
```

**<u>规则</u>** 前提交换.

由于我们定义的语境 (公式的列表) 是顺序敏感的, 所以需要此规则, 而对于理论 (公式的集合) 则不需要.

```agda
Swap : φ ∷ ψ ∷ Γ ⊢ ξ → ψ ∷ φ ∷ Γ ⊢ ξ
Swap {φ} {ψ} {Γ} {ξ} H =
                ∅─⟨ H ⟩
  φ ∷ ψ ∷ Γ ⊢ ξ ─⟨ Wkn sub ⟩
  ψ ∷ φ ∷ Γ ⊢ ξ
  where
  sub : φ ∷ ψ ∷ Γ ⊆ᴸ ψ ∷ φ ∷ Γ
  sub (here refl) = there (here refl)
  sub (there (here refl)) = here refl
  sub (there (there H)) = there (there H)
```

**<u>规则</u>** `Wkn` 的变体.

```agda
Wkn1 : φ ∷ Γ ⊢ ξ → φ ∷ ψ ∷ Γ ⊢ ξ
Wkn1 {φ} {Γ} {ξ} {ψ} H =
                ∅─⟨ H ⟩
  φ ∷ Γ ⊢ ξ     ─⟨ Wkn0 ⟩
  ψ ∷ φ ∷ Γ ⊢ ξ ─⟨ Swap ⟩
  φ ∷ ψ ∷ Γ ⊢ ξ
```

## 演绎定理

**<u>规则</u>** `ImpI` 的逆命题.  
**<u>证明</u>** 将前提 `Γ ⊢ φ →̇ ψ` 弱化成 `φ ∷ Γ ⊢ φ →̇ ψ`, 又由语境规则有 `φ ∷ Γ ⊢ φ`. 使用原版 `ImpE` 即得 `φ ∷ Γ ⊢ ψ`. ∎

```agda
ImpE′ : Γ ⊢ φ →̇ ψ → φ ∷ Γ ⊢ ψ
ImpE′ {Γ} {φ} {ψ} H = ImpE H₁ H₂ where
  H₁ =            ∅─⟨ H ⟩
    Γ ⊢ φ →̇ ψ     ─⟨ Wkn0 ⟩
    φ ∷ Γ ⊢ φ →̇ ψ
  H₂ =            ∅─⟨ Ctx0 ⟩
    φ ∷ Γ ⊢ φ
```

演绎定理是一条非常重要的元定理, 它表明了语法蕴含与实质蕴含的关系. 在我们的系统中, 它的证明是相对简单的.

**<u>定理</u>** 演绎定理: `φ ∷ Γ ⊢ ψ` 与 `Γ ⊢ φ →̇ ψ` 逻辑等价.  
**<u>证明</u>** 由 `ImpI` 和 `ImpE′` 即得. ∎

```agda
Deduction : φ ∷ Γ ⊢ ψ ↔ Γ ⊢ φ →̇ ψ
Deduction = ⇒: ImpI ⇐: ImpE′
```

## 切消

切削规则允许我们在证明中引入一个新的前提, 并通过该前提来证明原目标, 它有内外两种版本.

**<u>规则</u>** 切消 (外).

```agda
Cut : ∀ φ → Γ ⊢ φ → φ ∷ Γ ⊢ ψ → Γ ⊢ ψ
Cut {Γ} {ψ} φ H₁ H₂ = ImpE H₃ H₁ where
  H₃ =        ∅─⟨ H₂ ⟩
    φ ∷ Γ ⊢ ψ ─⟨ ImpI ⟩
    Γ ⊢ φ →̇ ψ
```

**<u>规则</u>** 切消 (内).

```agda
ImpCut : ∀ ψ → Γ ⊢ φ →̇ ψ → Γ ⊢ ψ →̇ ξ → Γ ⊢ φ →̇ ξ
ImpCut {Γ} {φ} {ξ} ψ H₁ H₂ =
              ∅─⟨ Cut ψ H₃ H₄ ⟩
  φ ∷ Γ ⊢ ξ   ─⟨ ImpI ⟩
  Γ ⊢ φ →̇ ξ
  where
  H₃ =        ∅─⟨ H₁ ⟩
    Γ ⊢ φ →̇ ψ ─⟨ ImpE′ ⟩
    φ ∷ Γ ⊢ ψ
  H₄ =        ∅─⟨ H₂ ⟩
    Γ ⊢ ψ →̇ ξ ─⟨ ImpE′ ⟩
    ψ ∷ Γ ⊢ ξ ─⟨ Wkn1 ⟩
    ψ ∷ φ ∷ Γ ⊢ ξ
```

## 局部无名

借助“未使用变元”的概念, 我们可以表述所谓**局部无名 (locally nameless)** 变换, 并且利用替换弱化规则, 我们可以证明它.

**<u>规则</u>** 局部无名变换: 如果 `n` 在 `Γ` 以及 `∀̇ φ` 中未使用, 那么 `⇞ Γ ⊢ φ` 与 `Γ ⊢ φ [ # n ]₀` 逻辑等价.  
**<u>证明</u>** 左边到右边, 如以下演绎得证.

```agda
nameless-conversion : fresh n Γ → freshᵩ n (∀̇ φ) → ⇞ Γ ⊢ φ ↔ Γ ⊢ φ [ # n ]₀
nameless-conversion {n} {Γ} {φ} freshΓ (fresh∀̇ freshᵩ-suc) =
  ⇒: (λ H →         ∅─⟨ H ⟩
    ⇞ Γ ⊢ φ         ─⟨ AllI ⟩
    Γ ⊢ ∀̇ φ         ─⟨ AllE ⟩
    Γ ⊢ φ [ # n ]₀  )
```

右边到左边, 要证 `Γ ⊢ φ [ # n ]₀` 蕴含 `⇞ Γ ⊢ φ`. 整体思路是找到一个替换 `ζ n`, 同时作用于 `Γ ⊢ φ [ # n ]₀` 的两边, 得到的 `⊢` 式由 `SubstWkn` 也成立, 并且正好等于 `⇞ Γ ⊢ φ`.

```agda
  ⇐: (λ Γ⊢φ[n] → subst2 (_⊢_) eq1 eq2 (SubstWkn (ζ n) Γ⊢φ[n]))
  where
```

`ζ n` 的定义如下: 对任意 `k : ℕ`, 如果它等于 `n`, 那么将它替换为 `# 0`, 否则替换为 `# (suc k)`. 其实际效果简单理解就是将 `# n` 指定为了本来由 `# 0` 承担的角色, 术语叫绑定子 (binder). 所以 `ζ` 也叫绑定子切换函数. 如下代码注释给出了一个实例: 将 `# 4` 切换为绑定子.

```agda
  -- switch binder to n
  -- k   = 0 1 2 3 4 5 6 ...
  -- ζ 4 = 1 2 3 4 0 6 7 ...
  ζ : ℕ → Subst
  ζ n = λ k → if does (k ≟ n) then # 0 else # (suc k)
```

为了证明 `Γ ⊢ φ [ # n ]₀` 两边同时做 `ζ n` 后与 `⇞ Γ ⊢ φ` 相等, 我们需要先证明 `ζ` 的两个性质.

`ζ` 的性质一: 如果 `n` 是 `φ` 的新变元, 那么 `φ [ ζ n ]ᵩ` 等于 `↑ φ`. 其证明可以从如下代码注释去理解, 其中 `# 4` 是新变元.

```agda
  -- k        = 0 1 2 3 | 4
  -- [ ζ 4 ]ᵩ = 1 2 3 4 | 0
  ζ-lift : ∀ n φ → freshᵩ n φ → φ [ ζ n ]ᵩ ≡ ↑ φ
  ζ-lift n φ Hfresh = []ᵩ-ext-freshᵩ Hfresh H where
    H : ∀ m → m ≢ n → ζ n m ≡ # (suc m)
    H m m≢n with m ≡ᵇ n in m≡ᵇn
    ... | true = exfalso $ m≢n $ ≡ᵇ⇒≡ _ _ $ subst 𝖳 m≡ᵇn tt
    ... | false = refl
```

`ζ` 的性质二: 如果 `suc n` 是 `φ` 的新变元, 那么 `φ` 的 `# n` 应用再做 `ζ n` 等于 `φ`. 其证明可以从如下代码注释去理解, 其中 `# 4` 是新变元.

```agda
  -- k                 = 0 1 2 3 | 4
  -- [ # 3 ]₀          = 3 0 1 2 | 4
  -- [ # 3 ]₀ [ ζ 3 ]ᵩ = 0 1 2 3 | 4
  ζ-id : ∀ n φ → freshᵩ (suc n) φ → φ [ # n ]₀ [ ζ n ]ᵩ ≡ φ
  ζ-id n φ Hfresh =
    φ [ # n ]₀ [ ζ n ]ᵩ           ≡⟨ []ᵩ-∘ φ ⟩
    φ [ _[ ζ n ]ₜ ∘ (# n ∷ₙ #) ]ᵩ ≡⟨ []ᵩ-ext-freshᵩ Hfresh H ⟩
    φ [ # ]ᵩ                      ≡⟨ [#]ᵩ ⟩
    φ                             ∎ where
    H : ∀ m → m ≢ suc n → (# n ∷ₙ #) m [ ζ n ]ₜ ≡ # m
    H zero _ with n ≡ᵇ n in n≡ᵇn
    ... | true = refl
    ... | false = exfalso $ subst 𝖳 (sym n≡ᵇn) (≡⇒≡ᵇ n _ refl)
    H (suc m) sm≢sn with m ≡ᵇ n in m≡ᵇn
    ... | true = exfalso $ sm≢sn $ cong suc $ ≡ᵇ⇒≡ _ _ $ subst 𝖳 m≡ᵇn tt
    ... | false = refl
```

最后, 使用`ζ` 的性质一以及 `map` 的外延性可证 `map (_[ ζ n ]ᵩ) Γ ≡ ⇞ Γ`.

```agda
  eq1 : map (_[ ζ n ]ᵩ) Γ ≡ ⇞ Γ
  eq1 = map-ext (λ φ φ∈Γ → ζ-lift n φ (freshΓ φ∈Γ))
```

使用本引理的前提消去 `ζ` 的性质二的前件, 即证 `φ [ # n ]₀ [ ζ n ]ᵩ ≡ φ`. ∎

```agda
  eq2 : φ [ # n ]₀ [ ζ n ]ᵩ ≡ φ
  eq2 = ζ-id n φ freshᵩ-suc
```

**<u>规则</u>** 局部无名变换 (使用对 `∀̇ φ` 和 `Γ` 来说都未使用的变元消掉上述规则的两个前件后的规则).

```agda
Nameless : ⇞ Γ ⊢ φ ↔ Γ ⊢ φ [ # $ freshVar $ ∀̇ φ ∷ Γ ]₀
Nameless {Γ} {φ} = nameless-conversion (freshVar∷-fresh (∀̇ φ) Γ) (freshVar∷-freshᵩ (∀̇ φ) Γ)
```

**<u>规则</u>** `AllI` 的变体: 如果 `n` 在 `Γ` 以及 `∀̇ φ` 中未使用, 那么 `Γ ⊢ φ [ # n ]₀` 蕴含 `Γ ⊢ ∀̇ φ`.

```agda
AllI′ : Γ ⊢ φ [ # $ freshVar $ ∀̇ φ ∷ Γ ]₀ → Γ ⊢ ∀̇ φ
AllI′ {Γ} {φ} H =
                ∅─⟨ H ⟩
  Γ ⊢ φ [ _ ]₀  ─⟨ Nameless .⇐ ⟩
  ⇞ Γ ⊢ φ       ─⟨ AllI ⟩
  Γ ⊢ ∀̇ φ
```

**<u>重言式</u>** `∀̇` 对 `→̇` 分配.

```agda
AllDistrbImp : *⊢ ∀̇ (φ →̇ ψ) → *⊢ ∀̇ φ →̇ ∀̇ ψ
AllDistrbImp {φ} {ψ} H₁ = ImpI′ H₂
  where
  H₂ : Γ ⊢ (∀̇ φ) → Γ ⊢ (∀̇ ψ)
  H₂ {Γ} H₃ =                 ∅─⟨ ImpE H₄ H₅ ⟩
    Γ ⊢ ψ [ _ ]₀              ─⟨ AllI′ ⟩
    Γ ⊢ (∀̇ ψ)
    where
    H₄ =                      ∅─⟨ H₁ ⟩
      Γ ⊢ ∀̇ (φ →̇ ψ)           ─⟨ AllE ⟩
      Γ ⊢ φ [ _ ]₀ →̇ ψ [ _ ]₀
    H₅ =                      ∅─⟨ H₃ ⟩
      Γ ⊢ (∀̇ φ)               ─⟨ AllE ⟩
      Γ ⊢ φ [ _ ]₀
```

## 排中律

**<u>定义</u>** 否定: 我们把 `φ →̇ ⊥̇` 简记作 `¬̇ φ`.

```agda
¬̇_ : Formula → Formula
¬̇ φ = φ →̇ ⊥̇
```

**<u>规则</u>** 虚空真.

```agda
Vac0 : φ ∷ Γ ⊢ ⊥̇ → Γ ⊢ φ →̇ ξ
Vac0 {φ} {Γ} {ξ} H =
              ∅─⟨ H ⟩
  φ ∷ Γ ⊢ ⊥̇   ─⟨ FalseE ⟩
  φ ∷ Γ ⊢ ξ   ─⟨ ImpI ⟩
  Γ ⊢ φ →̇ ξ

Vac1 : φ ∷ Γ ⊢ ψ → ¬̇ ψ ∷ Γ ⊢ φ →̇ ξ
Vac1 {φ} {Γ} {ψ} {ξ} H =
                    ∅─⟨ H ⟩
  φ ∷ Γ ⊢ ψ         ─⟨ App ⟩
  ψ →̇ ⊥̇ ∷ φ ∷ Γ ⊢ ⊥̇ ─⟨ FalseE ⟩
  ψ →̇ ⊥̇ ∷ φ ∷ Γ ⊢ ξ ─⟨ Swap ⟩
  φ ∷ ψ →̇ ⊥̇ ∷ Γ ⊢ ξ ─⟨ ImpI ⟩
  ¬̇ ψ ∷ Γ ⊢ φ →̇ ξ
```

**<u>规则</u>** 反证法.

```agda
Contra : ¬̇ φ ∷ Γ ⊢ ⊥̇ → Γ ⊢ φ
Contra {φ} {Γ} H = ImpE H₁ H₂ where
  H₁ =                    ∅─⟨ Peirce φ ⊥̇ ⟩
    Γ ⊢ ((φ →̇ ⊥̇) →̇ φ) →̇ φ
  H₂ =                    ∅─⟨ H ⟩
    φ →̇ ⊥̇ ∷ Γ ⊢ ⊥̇         ─⟨ FalseE ⟩
    φ →̇ ⊥̇ ∷ Γ ⊢ φ         ─⟨ ImpI ⟩
    Γ ⊢ (φ →̇ ⊥̇) →̇ φ
```

**<u>规则</u>** 排中律.

```agda
LEM : ∀ φ → φ ∷ Γ ⊢ ψ → ¬̇ φ ∷ Γ ⊢ ψ → Γ ⊢ ψ
LEM {Γ} {ψ} φ H₁ H₂ =     ∅─⟨ Cut (¬̇ φ) H₃ H₄ ⟩
  ¬̇ ψ ∷ Γ ⊢ ⊥̇             ─⟨ Contra ⟩
  Γ ⊢ ψ
  where
  H₃ =                    ∅─⟨ H₁ ⟩
    φ ∷ Γ ⊢ ψ             ─⟨ App ⟩
    ψ →̇ ⊥̇ ∷ φ ∷  Γ ⊢ ⊥̇    ─⟨ Swap ⟩
    φ ∷ ψ →̇ ⊥̇ ∷ Γ ⊢ ⊥̇     ─⟨ ImpI ⟩
    ψ →̇ ⊥̇ ∷ Γ ⊢ (¬̇ φ)
  H₄ =                    ∅─⟨ H₂ ⟩
    ¬̇ φ ∷ Γ ⊢ ψ           ─⟨ App ⟩
    ψ →̇ ⊥̇ ∷ (¬̇ φ) ∷ Γ ⊢ ⊥̇ ─⟨ Swap ⟩
    (¬̇ φ) ∷ ψ →̇ ⊥̇ ∷ Γ ⊢ ⊥̇
```

**<u>重言式</u>** 双重否定消去.

```agda
DNE : *⊢ ¬̇ ¬̇ φ →̇ φ
DNE {φ} {Γ} =                   ∅─⟨ Ctx0 ⟩
  (φ →̇ ⊥̇) →̇ ⊥̇ ∷ Γ ⊢ (φ →̇ ⊥̇) →̇ ⊥̇ ─⟨ ImpE′ ⟩
  ¬̇ φ ∷ ¬̇ ¬̇ φ ∷ Γ ⊢ ⊥̇           ─⟨ Contra ⟩
  ¬̇ ¬̇ φ ∷ Γ ⊢ φ                 ─⟨ ImpI ⟩
  Γ ⊢ ¬̇ ¬̇ φ →̇ φ
```

**<u>规则</u>** 蕴含式的否定的消去.

```agda
NImpE : Γ ⊢ ¬̇ (φ →̇ ψ) → Γ ⊢ φ
NImpE {Γ} {φ} {ψ} H =   ∅─⟨ ImpE H₁ H₂ ⟩
  ¬̇ φ ∷ Γ ⊢ ⊥̇           ─⟨ Contra ⟩
  Γ ⊢ φ
  where
  H₁ =                  ∅─⟨ H ⟩
    Γ ⊢ ¬̇ (φ →̇ ψ)       ─⟨ Wkn0 ⟩
    ¬̇ φ ∷ Γ ⊢ ¬̇ (φ →̇ ψ)
  H₂ =                  ∅─⟨ Ctx0 ⟩
    φ ∷ Γ ⊢ φ           ─⟨ Vac1 ⟩
    ¬̇ φ ∷ Γ ⊢ φ →̇ ψ
```

## 饮者悖论

**<u>定义</u>** 存在量化: 我们把 `¬̇ ∀̇ ¬̇ φ` 简记作 `∃̇ φ`.

```agda
∃̇_ : Formula → Formula
∃̇ φ = ¬̇ ∀̇ ¬̇ φ
```

**<u>规则</u>** 存在量词的引入.

```agda
ExI : ∀ t → Γ ⊢ φ [ t ]₀ → Γ ⊢ ∃̇ φ
ExI {Γ} {φ} t H =               ∅─⟨ Cut (¬̇ φ [ t ]₀) H₁ H₂ ⟩
  ∀̇ ¬̇ φ ∷ Γ ⊢ ⊥̇                 ─⟨ ImpI ⟩
  Γ ⊢ ∃̇ φ
  where
  H₁ =                          ∅─⟨ Ctx0 ⟩
    ∀̇ ¬̇ φ ∷ Γ ⊢ ∀̇ ¬̇ φ           ─⟨ AllE ⟩
    ∀̇ ¬̇ φ ∷ Γ ⊢ ¬̇ φ [ t ]₀
  H₂ =                          ∅─⟨ H ⟩
    Γ ⊢ φ [ t ]₀                ─⟨ Wkn0 ⟩
    ∀̇ ¬̇ φ ∷ Γ ⊢ φ [ t ]₀        ─⟨ App ⟩
    ¬̇ φ [ t ]₀ ∷ ∀̇ ¬̇ φ ∷ Γ ⊢ ⊥̇
```

**<u>规则</u>** 存在量词的消去.

```agda
ExE : Γ ⊢ ∃̇ φ → φ ∷ ⇞ Γ ⊢ ↑ ψ → Γ ⊢ ψ
ExE {Γ} {φ} {ψ} H₁ H₂ =     ∅─⟨ Cut (∀̇ ¬̇ φ) H₃ H₄ ⟩
  ¬̇ ψ ∷ Γ ⊢ ⊥̇               ─⟨ Contra ⟩
  Γ ⊢ ψ
  where
  H₃ =                      ∅─⟨ H₂ ⟩
    φ ∷ ⇞ Γ ⊢ ↑ ψ           ─⟨ App ⟩
    ↑ ψ →̇ ⊥̇ ∷ φ ∷ ⇞ Γ ⊢ ⊥̇   ─⟨ Swap ⟩
    φ ∷ ↑ ψ →̇ ⊥̇ ∷ ⇞ Γ ⊢ ⊥̇   ─⟨ ImpI ⟩
    ↑ ψ →̇ ⊥̇ ∷ ⇞ Γ ⊢ ¬̇ φ     ─⟨ AllI ⟩
    ψ →̇ ⊥̇ ∷ Γ ⊢ ∀̇ ¬̇ φ
  H₄ =                      ∅─⟨ H₁ ⟩
    Γ ⊢ ∃̇ φ                 ─⟨ Wkn0 ⟩
    ψ →̇ ⊥̇ ∷ Γ ⊢ ∃̇ φ         ─⟨ ImpE′ ⟩
    ∀̇ ¬̇ φ ∷ ψ →̇ ⊥̇ ∷ Γ ⊢ ⊥̇
```

**<u>规则</u>** 存在量词的消去加引入.

```agda
ExEI : φ ∷ ⇞ Γ ⊢ ψ → ∃̇ φ ∷ Γ ⊢ ∃̇ ψ
ExEI {φ} {Γ} {ψ} H = ExE Ctx0 $           ∅─⟨ H ⟩
  φ ∷ ⇞ Γ ⊢ ψ                             ─⟨ subst (_ ⊢_) ↑ₛ[]₀ ⟩
  φ ∷ ⇞ Γ ⊢ ψ [ ↑ₛ (# ∘ suc) ]ᵩ [ # 0 ]₀  ─⟨ ExI (# 0) ⟩
  φ ∷ ⇞ Γ ⊢ ↑ ∃̇ ψ                         ─⟨ Wkn1 ⟩
  φ ∷ ↑ ∃̇ φ ∷ ⇞ Γ ⊢ ↑ ∃̇ ψ
```

**<u>重言式</u>** “不存在否”蕴含“所有都是”.

```agda
NotExNotAll : *⊢ ¬̇ ∃̇ ¬̇ φ →̇ ∀̇ φ
NotExNotAll {φ} {Γ} = ImpCut (∀̇ ¬̇ ¬̇ φ) H₁ (AllDistrbImp H₂)
  where
  H₁ =                    ∅─⟨ DNE ⟩
    Γ ⊢ ¬̇ ∃̇ ¬̇ φ →̇ ∀̇ ¬̇ ¬̇ φ
  H₂ : *⊢ ∀̇ (¬̇ ¬̇ φ →̇ φ)
  H₂ {Γ} =                ∅─⟨ DNE ⟩
    ⇞ Γ ⊢ ¬̇ ¬̇ φ →̇ φ       ─⟨ AllI ⟩
    Γ ⊢ ∀̇ (¬̇ ¬̇ φ →̇ φ)
```

**<u>重言式</u>** 饮者“悖论”: 存在一个人, 如果他喝酒, 那么所有人都喝酒.

```agda
DP : *⊢ ∃̇ (φ →̇ ↑ ∀̇ φ)
DP {φ} {Γ} = LEM (∃̇ (¬̇ φ)) H₁ H₂ where
  H₁ =                                  ∅─⟨ Ctx0 ⟩
    φ ∷ ⇞ Γ ⊢ φ                         ─⟨ Vac1 ⟩
    ¬̇ φ ∷ ⇞ Γ ⊢ φ →̇ ↑ ∀̇ φ               ─⟨ ExEI ⟩
    ∃̇ ¬̇ φ ∷ Γ ⊢ ∃̇ (φ →̇ ↑ ∀̇ φ)
  H₂ =                                  ∅─⟨ NotExNotAll ⟩
    Γ ⊢ ¬̇ ∃̇ ¬̇ φ →̇ ∀̇ φ                   ─⟨ ImpE′ ⟩
    ¬̇ ∃̇ ¬̇ φ ∷ Γ ⊢ ∀̇ φ                   ─⟨ subst (¬̇ ∃̇ ¬̇ φ ∷ Γ ⊢_) ↑[]₀ ⟩
    ¬̇ ∃̇ ¬̇ φ ∷ Γ ⊢ (↑ ∀̇ φ) [ # 0 ]₀      ─⟨ WknImpI ⟩
    ¬̇ ∃̇ ¬̇ φ ∷ Γ ⊢ (φ →̇ ↑ ∀̇ φ) [ # 0 ]₀  ─⟨ ExI (# 0) ⟩
    ¬̇ ∃̇ ¬̇ φ ∷ Γ ⊢ ∃̇ (φ →̇ ↑ ∀̇ φ)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/AdmissibleRules.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.AdmissibleRules.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.admissible)  
> 交流Q群: 893531731
