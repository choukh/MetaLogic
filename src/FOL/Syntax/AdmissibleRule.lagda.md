---
url: fol.syntax.admissible
---

# 一阶逻辑 ▸ 语法 ▸ 可容许规则


若在一个形式系统中添加一个推理规则后, 该系统的定理集合不发生变化, 则称该推理规则在该形式系统中是**可容许的 (admissible)**. 换句话说, 使用该规则可证明的每个公式在没有该规则的情况下已经是可证明的. 因此在某种程度上说, 该规则是冗余的. 但是对于研究这个系统而言, 它们是重要引理.

```agda
open import Foundation.Essential
open import Foundation.Relation.Nullary.Discrete.List

open import FOL.Language
module FOL.Syntax.AdmissibleRule (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
open import FOL.Syntax.SubstitutionFacts ℒ

open import FOL.Syntax.Discrete ℒ
open SetOperation (discreteSet {A = Formula})

private variable
  n : ℕ
```

## 语境

**<u>引理</u>** TODO.  
**<u>证明</u>** TODO. ∎

```agda
Ctx0 : φ ∷ Γ ⊢ φ
Ctx0 = Ctx $ here refl

Ctx1 : ψ ≡ ξ → φ ∷ ψ ∷ Γ ⊢ ξ
Ctx1 refl = Ctx $ there (here refl)
```

### 弱化

弱化指的是对语境的弱化. 此类规则允许我们通过在弱化的语境中证明某公式, 来说明原语境中就能证明该公式.

**<u>引理</u>** 弱化规则: `Γ ⊆ᴸ Δ` 蕴含 `Γ ⊢ φ → Δ ⊢ φ`.
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

**<u>引理</u>** TODO.  
**<u>证明</u>** TODO. ∎

```agda
Wkn0 : Γ ⊢ ψ → φ ∷ Γ ⊢ ψ
Wkn0 = Wkn there
```

**<u>引理</u>** `ImpI` 的弱化: 可以通过证明蕴含式的右边可证明来证明该蕴含式.  
**<u>证明</u>** 由 `ImpI` 和弱化规则即得. ∎

```agda
WknImpI : Γ ⊢ ψ → Γ ⊢ φ →̇ ψ
WknImpI = ImpI ∘ Wkn0
```

**<u>引理</u>** TODO.  
**<u>证明</u>** TODO. ∎

```agda
Swap : φ ∷ ψ ∷ Γ ⊢ ξ → ψ ∷ φ ∷ Γ ⊢ ξ
Swap = Wkn H where
  H : φ ∷ ψ ∷ Γ ⊆ᴸ ψ ∷ φ ∷ Γ
  H (here refl) = there (here refl)
  H (there (here refl)) = here refl
  H (there (there H)) = there (there H)
```

**<u>引理</u>** TODO.  
**<u>证明</u>** TODO. ∎

```agda
Wkn1 : φ ∷ Γ ⊢ ξ → φ ∷ ψ ∷ Γ ⊢ ξ
Wkn1 = Swap ∘ Wkn0
```

### 替换

**<u>引理</u>** 替换弱化规则: 一个证明在其语境和结论同时做同种替换后仍然有效.  
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
有归纳假设 `map (_[ ↑ₛ σ ]ᵩ) (↑ Γ) ⊢ φ [ ↑ₛ σ ]ᵩ`.
对目标使用 `AllI` 归纳, 只要证 `↑ (map (_[ σ ]ᵩ) Γ) ⊢ φ [ ↑ₛ σ ]ᵩ`.
将目标 `⊢` 式的左边换成 `map (_[ ↑ₛ σ ]ᵩ) (↑ Γ)` 即证. ∎

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

## 蕴含

**<u>引理</u>** `ImpI` 的变体: TODO.  
**<u>证明</u>** TODO. ∎

```agda
ImpI′ : (∀ Γ → Γ ⊢ φ → Γ ⊢ ψ) → Γ ⊢ φ →̇ ψ
ImpI′ H = ImpI (H _ Ctx0)
```

**<u>引理</u>** 蕴含式的应用: TODO.  
**<u>证明</u>** TODO. ∎

```agda
App : Γ ⊢ φ → φ →̇ ψ ∷ Γ ⊢ ψ
App H = ImpE Ctx0 (Wkn0 H)
```

### 演绎定理

**<u>引理</u>** `ImpI` 的逆命题成立.  
**<u>证明</u>** 将前提 `Γ ⊢ φ →̇ ψ` 弱化成 `φ ∷ Γ ⊢ φ →̇ ψ`, 又由语境规则有 `φ ∷ Γ ⊢ φ`. 使用原版 `ImpE` 即得 `φ ∷ Γ ⊢ ψ`. ∎

```agda
ImpE′ : Γ ⊢ φ →̇ ψ → φ ∷ Γ ⊢ ψ
ImpE′ Γ⊢ = ImpE (Wkn0 Γ⊢) Ctx0
```

演绎定理是一条非常重要的元定理, 它表明了语法蕴含与实质蕴含的关系. 在我们的系统中, 它的证明是相对简单的.

**<u>定理</u>** 演绎定理: `φ ∷ Γ ⊢ ψ` 与 `Γ ⊢ φ →̇ ψ` 逻辑等价.  
**<u>证明</u>** 由 `ImpI` 和 `ImpE′` 即得. ∎

```agda
Deduction : φ ∷ Γ ⊢ ψ ↔ Γ ⊢ φ →̇ ψ
Deduction = ⇒: ImpI ⇐: ImpE′
```

### 切消

**<u>引理</u>** 切消规则: TODO.  
**<u>证明</u>** TODO. ∎

```agda
Cut : ∀ φ → Γ ⊢ φ → φ ∷ Γ ⊢ ψ → Γ ⊢ ψ
Cut _ = flip (ImpE ∘ ImpI)

ImpCut : ∀ ψ → Γ ⊢ φ →̇ ψ → Γ ⊢ ψ →̇ ξ → Γ ⊢ φ →̇ ξ
ImpCut ψ H₁ H₂ = ImpI $ Cut ψ (ImpE′ H₁) (Wkn1 $ ImpE′ H₂)
```

## 全称量化

借助“未使用变元”的概念, 我们可以表述所谓**局部无名 (locally nameless)** 变换, 并且利用替换弱化规则, 我们可以证明它.

**<u>引理</u>** 局部无名变换: 如果 `n` 在 `Γ` 以及 `∀̇ φ` 中未使用, 那么 `↑ Γ ⊢ φ` 与 `Γ ⊢ φ [ # n ]₀` 逻辑等价.  
**<u>证明</u>** TODO. ∎

```agda
nameless-conversion : fresh n Γ → freshᵩ n (∀̇ φ) → ↑ Γ ⊢ φ ↔ Γ ⊢ φ [ # n ]₀
nameless-conversion {n} {Γ} {φ} freshΓ (fresh∀̇ freshᵩ-suc) =
  ⇒: AllE ∘ AllI
  ⇐: λ Γ⊢φ[n] → subst2 (_⊢_) eq1 eq2 (SubstWkn (ζ n) Γ⊢φ[n])
  where
  -- switch binder to n
  -- k   = 0 1 2 3 4 5 6 ...
  -- ζ 4 = 1 2 3 4 0 6 7 ...
  ζ : ℕ → Subst
  ζ n = λ k → if does (k ≟ n) then # 0 else # (suc k)
  -- k        = 0 1 2 3 | 4
  -- [ ζ 4 ]ᵩ = 1 2 3 4 | 0
  ζ-lift : ∀ n φ → freshᵩ n φ → φ [ ζ n ]ᵩ ≡ ↑ᵩ φ
  ζ-lift n φ Hfresh = []ᵩ-ext-freshᵩ Hfresh H where
    H : ∀ m → m ≢ n → ζ n m ≡ # (suc m)
    H m m≢n with m ≡ᵇ n in m≡ᵇn
    ... | true = exfalso $ m≢n $ ≡ᵇ⇒≡ _ _ $ subst 𝖳 m≡ᵇn tt
    ... | false = refl
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
  eq1 : map (_[ ζ n ]ᵩ) Γ ≡ ↑ Γ
  eq1 = map-ext (λ φ φ∈Γ → ζ-lift n φ (freshΓ φ∈Γ))
  eq2 : (φ [ # n ]₀) [ ζ n ]ᵩ ≡ φ
  eq2 = ζ-id n φ freshᵩ-suc
```

**<u>引理</u>** 全称量化的引入规则 (变体): 如果 `n` 在 `Γ` 以及 `∀̇ φ` 中未使用, 那么 `Γ ⊢ φ [ # n ]₀` 蕴含 `Γ ⊢ ∀̇ φ`.  
**<u>证明</u>** 由局部无名变换及 `AllI` 即得. ∎

```agda
AllI′ : Γ ⊢ φ [ # $ freshVar $ ∀̇ φ ∷ Γ ]₀ → Γ ⊢ ∀̇ φ
AllI′ {Γ} {φ} = AllI ∘ nameless-conversion (freshVar∷-fresh (∀̇ φ) Γ) (freshVar∷-freshᵩ (∀̇ φ) Γ) .⇐
```

**<u>重言式</u>** TODO.  
**<u>证明</u>** TODO. ∎

```agda
AllDistrbImp : ⊩ ∀̇ (φ →̇ ψ) → ⊩ ∀̇ φ →̇ ∀̇ ψ
AllDistrbImp ⊩∀̇ = ImpI′ λ Γ Γ⊢∀̇φ → AllI′ (ImpE (AllE ⊩∀̇) (AllE Γ⊢∀̇φ))
```

## 否定

**<u>定义</u>** 否定: 我们把 `φ →̇ ⊥̇` 简记作 `¬̇ φ`.

```agda
¬̇_ : Formula → Formula
¬̇ φ = φ →̇ ⊥̇
```

**<u>引理</u>** 反证法: TODO.  
**<u>证明</u>** TODO. ∎

```agda
Contra : ¬̇ φ ∷ Γ ⊢ ⊥̇ → Γ ⊢ φ
Contra {φ} H = ImpE (Peirce φ ⊥̇) (ImpI $ FalseE $ H)
```

**<u>引理</u>** 排中律: TODO.  
**<u>证明</u>** TODO. ∎

```agda
LEM : ∀ φ → φ ∷ Γ ⊢ ψ → ¬̇ φ ∷ Γ ⊢ ψ → Γ ⊢ ψ
LEM φ H₁ H₂ = Contra $ Cut (¬̇ φ)
  (ImpI $ Swap $ App H₁)
  (Swap $ App H₂)
```

**<u>重言式</u>** 双重否定消去: TODO.  
**<u>证明</u>** TODO. ∎

```agda
DNE : ⊩ ¬̇ ¬̇ φ →̇ φ
DNE = ImpI $ Contra $ ImpE′ Ctx0
```

## 存在量化

**<u>定义</u>** 存在量化: 我们把 `¬̇ ∀̇ ¬̇ φ` 简记作 `∃̇ φ`.

```agda
∃̇_ : Formula → Formula
∃̇ φ = ¬̇ ∀̇ ¬̇ φ
```

**<u>引理</u>** 存在量词的引入规则: TODO.  
**<u>证明</u>** TODO. ∎

```agda
ExI : ∀ t → Γ ⊢ φ [ t ]₀ → Γ ⊢ ∃̇ φ
ExI _ H = ImpI $ Cut _
  (AllE Ctx0)
  (App $ Wkn0 H)
```

**<u>引理</u>** 存在量词的消去规则: TODO.  
**<u>证明</u>** TODO. ∎

```agda
ExE : Γ ⊢ ∃̇ φ → φ ∷ ↑ Γ ⊢ ↑ᵩ ψ → Γ ⊢ ψ
ExE {φ} H₁ H₂ = Contra $ Cut (∀̇ ¬̇ φ)
  (AllI $ ImpI $ Swap $ App H₂)
  (ImpE′ $ Wkn0 H₁)
```

**<u>重言式</u>** TODO.  
**<u>证明</u>** TODO. ∎

```agda
NotExNotAll : ⊩ ¬̇ ∃̇ ¬̇ φ →̇ ∀̇ φ
NotExNotAll {φ} = ImpCut (∀̇ ¬̇ ¬̇ φ) DNE (AllDistrbImp $ AllI DNE)
```

**<u>重言式</u>** 饮者悖论: TODO.  
**<u>证明</u>** TODO. ∎

```agda
DP : ⊩ ∃̇ (φ →̇ ↑ᵩ (∀̇ φ))
DP {φ} {Γ} = LEM (∃̇ ¬̇ φ)
  (ExE (ExI (# 0) {!   !}) (Ctx1 {!   !}))
  (ExI (# 0) (ImpI $ Wkn0 $ subst (¬̇ ∃̇ ¬̇ φ ∷ Γ ⊢_) ↑ᵩ[]₀ (ImpE′ NotExNotAll)))
```

## 理论版规则

TODO

```agda
Ctxᵀ : φ ∈ 𝒯 → 𝒯 ⊢ᵀ φ
Ctxᵀ {φ} φ∈𝒯 = [ φ ] , (λ { (here refl) → φ∈𝒯 }) , Ctx0
```

```agda
ImpIᵀ : (𝒯 ⨭ φ) ⊢ᵀ ψ → 𝒯 ⊢ᵀ φ →̇ ψ
ImpIᵀ {𝒯} {φ} (Γ , Γ⊆𝒯⨭φ , Γ⊢) = Γ ∖[ φ ] , H1 , ImpI (Wkn H2 Γ⊢) where
  H1 : Γ ∖[ φ ] ᴸ⊆ᴾ 𝒯
  H1 {x} x∈ with ∈∖[]-elim x∈
  ... | x∈Γ , x≢φ = 𝟙.rec (isProp∈ {x = x} {𝒯}) H (Γ⊆𝒯⨭φ x∈Γ) where
    H : x ∈ 𝒯 ⊎ x ∈ ｛ φ ｝ → x ∈ 𝒯
    H (inj₁ p) = p
    H (inj₂ refl) = exfalso (x≢φ refl)
  H2 : Γ ⊆ᴸ φ ∷ Γ ∖[ φ ]
  H2 = ⊆ᴸ-trans {j = φ ∷ Γ} there ∷⊆∷∖[]
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/AdmissibleRule.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.AdmissibleRule.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.admissible)  
> 交流Q群: 893531731
