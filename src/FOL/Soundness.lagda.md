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

open import FOL.Syntax ℒ
open import FOL.Syntax.Properties ℒ
open import FOL.Semantics ℒ
open import FOL.Semantics.Properties ℒ
```

## 可靠性定理

**<u>定理</u>** `𝒞`-可靠性:
对任意包含爆炸变体的变体 `𝒞`, 对任意语境 `Γ` 和公式 `φ`, 如果 `Γ` 语法蕴含 `φ`, 那么 `Γ` `𝒞`-语义蕴含 `φ`.

```agda
soundness⟨_⟩ : (𝒞 : Variant ℓ) → Exp ⊑ 𝒞 →
  ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨⟨ 𝒞 ⟩ φ
```

**<u>递归证明</u>** 对语法蕴含 (证明树) 的构造方式归纳.

- 使用语境规则 `Ctx` 构造:
  - 证明树类型: `Γ ⊢ φ`
  - 构造的前提: `φ ∈ᴸ Γ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ φ`, 即 `𝓋 ⊨ₛ Γ → 𝓋 ⊨ᵩ φ`
  - 子证明: `𝓋 ⊨ₛ Γ` 是说 `φ ∈ᴸ Γ → 𝓋 ⊨ᵩ φ`. 而我们有前提 `φ ∈ᴸ Γ`, 所以目标蕴含式成立 ▫

```agda
soundness⟨ 𝒞 ⟩ _ (Ctx φ∈Γ) _ _ 𝓋⊨Γ = 𝓋⊨Γ _ φ∈Γ
```

- 使用蕴含的引入规则 `ImpI` 构造:
  - 证明树类型: `Γ ⊢ φ →̇ ψ`
  - 构造的前提: `(φ ∷ Γ) ⊢ ψ`
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
  - 构造的前提: `↑ Γ ⊢ φ`
  - 归纳假设: `↑ Γ ⊨⟨ 𝒞 ⟩ φ`, 可特化为 `x ∷ₙ 𝓋 ⊨ₛ ↑ Γ → x ∷ₙ 𝓋 ⊨ᵩ φ`
  - 子目标: `Γ ⊨⟨ 𝒞 ⟩ ∀̇ φ`, 即 `𝓋 ⊨ₛ Γ → x ∷ₙ 𝓋 ⊨ᵩ φ`
  - 子证明: 由归纳假设, 只需证 `𝓋 ⊨ₛ Γ → x ∷ₙ 𝓋 ⊨ₛ ↑ Γ`. 由引理 `map⊆P-intro`, 只需证对任意 `φ ∈ᴸ Γ` 有 `x ∷ₙ 𝓋 ⊨ᵩ ↑ᵩ x₁`. 由引理 `∷ₙ⊨ᵩ↑ᵩ`, 只需证 `𝓋 ⊨ᵩ φ`. 由前提 `𝓋 ⊨ₛ Γ` 和 `φ ∈ᴸ Γ` 得证. ▫

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (AllI H) c 𝓋 𝓋⊨Γ x = soundness⟨ 𝒞 ⟩ Γ⊢ H c (x ∷ₙ 𝓋) $
  map⊆P-intro λ φ φ∈Γ → ∷ₙ⊨ᵩ↑ᵩ x 𝓋 φ .⇒ $ 𝓋⊨Γ φ φ∈Γ
```

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (AllE {φ} {t} H) c 𝓋 𝓋⊨Γ = H1 where
  H1 : 𝓋 ⊨ᵩ φ [ t ∷]
  H1 = ⊨ᵩ-∘ 𝓋 φ (t ∷ₙ #_) .⇒ H2 where
    H2 : (𝓋 ⊨ₜ_ ∘ (t ∷ₙ #_)) ⊨ᵩ φ
    H2 = ⊨ᵩ-ext eq φ .⇒ H3 where
      H3 : ((𝓋 ⊨ₜ t) ∷ₙ 𝓋) ⊨ᵩ φ
      H3 = soundness⟨ 𝒞 ⟩ Γ⊢ H c 𝓋 𝓋⊨Γ (𝓋 ⊨ₜ t)
      eq : ∀ n → ((𝓋 ⊨ₜ t) ∷ₙ 𝓋) n ≡ 𝓋 ⊨ₜ (t ∷ₙ #_) n
      eq zero = refl
      eq (suc n) = refl
```

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (FalseE {φ} Γ⊢⊥̇) c 𝓋 𝓋⊨Γ = semanticExplosion (Γ⊢ c .snd) 𝓋 φ $ soundness⟨ 𝒞 ⟩ Γ⊢ Γ⊢⊥̇ c 𝓋 𝓋⊨Γ
```

```agda
soundness⟨ 𝒞 ⟩ Γ⊢ (Peirce φ ψ) c 𝓋 _ = Γ⊢ c .fst 𝓋 φ ψ
```

**<u>推论</u>** 可靠性: 对任意语境 `Γ` 和公式 `φ`, 如果 `Γ` 语法蕴含 `φ`, 那么 `Γ` 语义蕴含 `φ`.  
**<u>证明</u>** 即证 `Std`-可靠性. 由于爆炸变体包含于标准变体, 由 `𝒞`-可靠性得证. ∎

```agda
soundness : Γ ⊢ φ → Γ ⊨ φ
soundness Γ⊢φ = soundness⟨ Std ⟩ Exp⊑Std Γ⊢φ
```

## 空语境下的一致性

```agda
instance
  ℐ : Interpretation ⊤
  ℐ = record
    { fᴵ = λ _ _ → tt
    ; Rᴵ = λ _ _ → ⊥ₚ
    ; ⊥ᴵ = ⊥ₚ }

Dec⊨ᵩ : (𝓋 : Valuation ⊤) (φ : Formula) → Dec (𝓋 ⊨ᵩ φ)
Dec⊨ᵩ 𝓋 ⊥̇       = no λ ()
Dec⊨ᵩ 𝓋 (R $̇ x) = no λ ()
Dec⊨ᵩ 𝓋 (φ →̇ ψ) with Dec⊨ᵩ 𝓋 φ | Dec⊨ᵩ 𝓋 ψ
... | yes p | yes q = yes λ _ → q
... | yes p | no ¬q = no λ pq → ¬q $ pq p
... | no ¬p | _     = yes λ p → exfalso $ ¬p p
Dec⊨ᵩ 𝓋 (∀̇ φ) with Dec⊨ᵩ (tt ∷ₙ 𝓋) φ
... | yes p = yes λ { tt → p }
... | no ¬p = no λ p → ¬p $ p tt

classical : Classical
classical 𝓋 φ ψ pierce with Dec⊨ᵩ 𝓋 φ
... | yes p = p
... | no ¬p = exfalso $ ¬p $ pierce λ p → exfalso $ ¬p p

consistency : [] ⊬ ⊥̇
consistency ⊢⊥̇ = soundness ⊢⊥̇ (classical , id) (λ _ → tt) λ _ ()
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Soundness.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Soundness.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.soundness)  
> 交流Q群: 893531731
