---
url: fol.soundness
---

# 一阶逻辑 ▸ 可靠性

我们介绍了一阶逻辑的语法和语义, 讲了什么是语法蕴含 (可证性), 什么是语义蕴含 (有效性).  
本篇将证明一阶逻辑重要定理: **可靠性定理 (soundness)**. 它说如果一个公式是可证的, 那么它是有效的.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Soundness (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Semantics.Base ℒ
open import FOL.Semantics.EvaluationFacts ℒ
```

## 可靠性定理

**<u>定理</u>** `𝒞`-可靠性:
对爆炸语义的任意子变体 `𝒞`, 以及任意语境 `Γ` 和公式 `φ`, 如果 `Γ` 语法蕴含 `φ`, 那么 `Γ` `𝒞`-语义蕴含 `φ`.

```agda
soundness⟨_⟩ : (𝒞 : Variant ℓ) → 𝒞 ⊑ Exp →
  ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨⟨ 𝒞 ⟩ φ
```

**<u>证明</u>** 对语法蕴含 (证明树) 的构造方式归纳.

- 使用语境规则 `Ctx` 构造:
  - 证明树类型: `Γ ⊢ φ`
  - 构造的前提: `φ ∈ᴸ Γ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ φ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ`
  - 子证明: `𝓋 ⊨ₛ Γ` 是说 `φ ∈ᴸ Γ → 𝓋 ⊨ᵩ φ`. 而我们有前提 `φ ∈ᴸ Γ`, 所以目标蕴含式成立. ▫

```agda
soundness⟨ 𝒞 ⟩ _ (Ctx φ∈Γ) _ _ 𝓋⊨Γ = 𝓋⊨Γ _ φ∈Γ
```

- 使用蕴含的引入规则 `ImpI` 构造:
  - 证明树类型: `Γ ⊢ φ →̇ ψ`
  - 构造的前提: `φ ∷ Γ ⊢ ψ`
  - 归纳假设: `φ ∷ Γ ⊨⟨ 𝒞 ⟩ ψ`, 即 `𝓋 ⊨ₛ φ ∷ Γ → 𝓋 ⊨ᵩ ψ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ φ →̇ ψ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ`
  - 子证明: 由归纳假设, 只需证 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ → 𝓋 ⊨ₛ φ ∷ Γ`. 由引理 `_⊨∷_` 得证. ▫
    ※ 主线中没有出现的引理 (例如这里提到的 `_⊨∷_`) 通常收集在了标题带上标减号的章节中, 读者可以全库搜索引理名找到它们. 如果找不到, 则只能在 [github 仓库](https://github.com/choukh/MetaLogic/tree/main)里找.

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (ImpI H) c 𝓋 𝓋⊨Γ 𝓋⊨φ = soundness⟨ 𝒞 ⟩ Γ⊢ H c 𝓋 (𝓋⊨φ ⊨∷ 𝓋⊨Γ)
```

- 使用蕴含的消去规则 `ImpE` 构造:
  - 证明树类型: `Γ ⊢ ψ`
  - 构造的前提:
    1. `Γ ⊢ φ →̇ ψ`
    2. `Γ ⊢ φ`
  - 归纳假设:
    1. `Γ ⊨⟨ 𝒞 ⟩ φ →̇ ψ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ ψ`
    2. `Γ ⊨⟨ 𝒞 ⟩ φ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ ψ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ ψ`
  - 子证明: 由归纳假设得证. ▫

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (ImpE H₁ H₂) c 𝓋 𝓋⊨Γ = soundness⟨ 𝒞 ⟩ Γ⊢ H₁ c 𝓋 𝓋⊨Γ $ soundness⟨ 𝒞 ⟩ Γ⊢ H₂ c 𝓋 𝓋⊨Γ
```

- 使用全称的引入规则 `AllI` 构造:
  - 证明树类型: `Γ ⊢ ∀̇ φ`
  - 构造的前提: `⇞ Γ ⊢ φ`
  - 归纳假设: `⇞ Γ ⊨⟨ 𝒞 ⟩ φ`, 可特化为 `x ∷ₙ 𝓋 ⊨ₛ ⇞ Γ → x ∷ₙ 𝓋 ⊨ᵩ φ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ ∀̇ φ`, 即 `𝓋 ⊨ₛ Γ → x ∷ₙ 𝓋 ⊨ᵩ φ`
  - 子证明: 由归纳假设, 只需证 `𝓋 ⊨ₛ Γ → x ∷ₙ 𝓋 ⊨ₛ ⇞ Γ`. 由引理 `map⊆P`, 只需证对任意 `φ ∈ᴸ Γ` 有 `x ∷ₙ 𝓋 ⊨ᵩ ↑ x₁`. 由引理 `∷ₙ⊨ᵩ↑`, 只需证 `𝓋 ⊨ᵩ φ`. 由前提 `𝓋 ⊨ₛ Γ` 和 `φ ∈ᴸ Γ` 得证. ▫

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (AllI H) c 𝓋 𝓋⊨Γ x = soundness⟨ 𝒞 ⟩ Γ⊢ H c (x ∷ₙ 𝓋) $
  map⊆P λ φ φ∈Γ → ∷ₙ⊨ᵩ↑ x 𝓋 φ .⇒ $ 𝓋⊨Γ φ φ∈Γ
```

- 使用全称的消去规则 `AllE` 构造:
  - 证明树类型: `Γ ⊢ φ [ t ]₀`
  - 构造的前提: `Γ ⊢ ∀̇ φ`
  - 归纳假设: `Γ ⊨⟨ 𝒞 ⟩ ∀̇ φ`, 可特化为 `𝓋 ⊨ₛ Γ → (𝓋 ⊨ₜ t) ∷ₙ 𝓋 ⊨ᵩ φ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ φ [ t ]₀`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ [ t ]₀`
  - 子证明: 由归纳假设只需证 `(𝓋 ⊨ₜ t) ∷ₙ 𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ φ [ t ]₀`, 这正是引理 `φ[t]-intro` 的结论. ▫

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (AllE {φ} {t} H) c 𝓋 𝓋⊨Γ = φ[t]-intro 𝓋 φ t (soundness⟨ 𝒞 ⟩ Γ⊢ H c 𝓋 𝓋⊨Γ (𝓋 ⊨ₜ t))
```

- 使用爆炸的消去规则 `FalseE` 构造:
  - 证明树类型: `Γ ⊢ φ`
  - 构造的前提: `Γ ⊢ ⊥̇`
  - 归纳假设: `Γ ⊨⟨ 𝒞 ⟩ ⊥̇`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ ⊥̇`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ φ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ`
  - 子证明: 由归纳假设只需证 `𝓋 ⊨ᵩ ⊥̇ → 𝓋 ⊨ᵩ φ`, 这正是引理 `semanticExplosion` 的结论. ▫

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (FalseE {φ} Γ⊢⊥̇) c 𝓋 𝓋⊨Γ = semanticExplosion (Γ⊢ c .snd) 𝓋 φ $ soundness⟨ 𝒞 ⟩ Γ⊢ Γ⊢⊥̇ c 𝓋 𝓋⊨Γ
```

- 使用皮尔士公理 `Peirce` 构造:
  - 证明树类型: `Γ ⊢ ((φ →̇ ψ) →̇ φ) →̇ φ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ ((φ →̇ ψ) →̇ φ) →̇ φ`
  - 子证明: 变体 `𝒞` 是经典变体, 所以子目标成立. ∎

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (Peirce φ ψ) c 𝓋 _ = Γ⊢ c .fst 𝓋 φ ψ
```

**<u>推论</u>** 有限可靠性: 对任意语境 `Γ` 和公式 `φ`, 如果 `Γ` 语法蕴含 `φ`, 那么 `Γ` 语义蕴含 `φ`.  
**<u>证明</u>** 即证 `Std`-可靠性. 由于爆炸变体包含于标准变体, 由 `𝒞`-可靠性得证. ∎

```agda
module _ {ℓ} where
  open PolymorphicSemantics ℓ

  finite-soundness : Γ ⊢ φ → Γ ⊨ φ
  finite-soundness Γ⊢φ = soundness⟨ Std ⟩ Std⊑Exp Γ⊢φ
```

**<u>推论</u>** 可靠性: 对任意理论 `𝒯` 和公式 `φ`, 如果 `𝒯` 语法蕴含 `φ`, 那么 `𝒯` 语义蕴含 `φ`.  
**<u>证明</u>** 依定义, 由有限可靠性即得. ∎

```
  soundness : 𝒯 ⊩ φ → 𝒯 ⊫ φ
  soundness (Γ , Γ⊆ , Γ⊢) std 𝓋 valid = finite-soundness Γ⊢ std 𝓋 λ φ φ∈Γ → valid φ (Γ⊆ φ∈Γ)
```

## 空语境下的一致性

可靠性定理的一个重要推论是空语境下的一致性, 也就是说空语境下不能证明假 (`[] ⊬ ⊥̇`). 我们先构造一个平凡的解释 `ℐ`, 证明在 `ℐ` 下任意 `𝓋 ⊨ᵩ φ` 都是可判定的, 从而证明 `ℐ` 是标准变体, 以套用可靠性定理证明 `[] ⊬ ⊥̇`.

**<u>构造</u>** 到单集 `⊤` 的符号解释 `ℐ`:
- 函数符号解释 `fᴵ`: 将所有函数符号一律映射到 一律取值为 `tt` 的函数. 其中 `tt` 是 `⊤` 的唯一元素.
- 关系符号解释 `Rᴵ`: 将所有关系符号一律映射到 一律取值为**假命题** `⊥ₚ` 的关系.
- 公式 `⊥̇` 的解释 `⊥ᴵ`: **假命题** `⊥ₚ`.

```agda
private instance
  ℐ : Interpretation ⊤
  ℐ = record
    { fᴵ = λ _ _ → tt
    ; Rᴵ = λ _ _ → ⊥ₚ
    ; ⊥ᴵ = ⊥ₚ }
```

**<u>注意</u>** 此解释下只有一种赋值, 那就是 `λ _ → tt`.

**<u>引理</u>** 在解释 `ℐ` 下, 任意 `𝓋 ⊨ᵩ φ` 都是可判定的.  
**<u>证明</u>** 由于 `ℐ` 把 `⊥̇` 和所有关系都解释到**假命题**, 对公式的结构归纳可证所有公式都判定为假. ∎

```agda
Dec⊨ᵩ : (𝓋 : Assignment ⊤) (φ : Formula) → Dec (𝓋 ⊨ᵩ φ)
Dec⊨ᵩ 𝓋 ⊥̇       = no λ ()
Dec⊨ᵩ 𝓋 (R $̇ x) = no λ ()
Dec⊨ᵩ 𝓋 (φ →̇ ψ) with Dec⊨ᵩ 𝓋 φ | Dec⊨ᵩ 𝓋 ψ
... | yes p | yes q = yes λ _ → q
... | yes p | no ¬q = no λ pq → ¬q $ pq p
... | no ¬p | _     = yes λ p → exfalso $ ¬p p
Dec⊨ᵩ 𝓋 (∀̇ φ) with Dec⊨ᵩ (tt ∷ₙ 𝓋) φ
... | yes p = yes λ { tt → p }
... | no ¬p = no λ p → ¬p $ p tt
```

**<u>引理</u>** `ℐ` 是经典变体.  
**<u>证明</u>** 即证 `ℐ` 使皮尔士公理有效. 判定 `𝓋 ⊨ᵩ φ`.

- `𝓋 ⊨ᵩ φ` 成立, 则立即有 `𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ`
- `𝓋 ⊨ᵩ φ` 不成立, 我们证 `𝓋 ⊨ᵩ ((φ →̇ ψ) →̇ φ) →̇ φ`. 展开定义, 只需证 `𝓋 ⊨ᵩ φ → 𝓋 ⊨ᵩ φ`. 前提矛盾. ∎

```agda
classical : Classical
classical 𝓋 φ ψ pierce with Dec⊨ᵩ 𝓋 φ
... | yes p = p
... | no ¬p = pierce λ p → exfalso $ ¬p p
```

**<u>定理</u>** 空语境下的一致性: `[] ⊬ ⊥̇`.  
**<u>证明</u>** 由于 `ℐ` 是经典变体, 且显然是爆炸⊥变体, 所以是标准变体, 可以使用可靠性定理. 假设 `[] ⊢ ⊥̇`, 由可靠性定理可以证明假, 所以 `[] ⊬ ⊥̇`. ∎

```agda
consistency : [] ⊬ ⊥̇
consistency ⊢⊥̇ = finite-soundness ⊢⊥̇ (classical , id) (λ _ → tt) λ _ ()
```

**<u>注意</u>** 我们自始至终没有在元语言中引入排中律.

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Soundness.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Soundness.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.soundness)  
> 交流Q群: 893531731
