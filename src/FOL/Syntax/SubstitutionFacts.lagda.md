---
url: fol.syntax.substitution
---

# 一阶逻辑 ▸ 语法 ▸ᐨ 替换的性质

这是一篇标题中带上标减号 (ᐨ) 的章节. 这表示这种章节不推荐线性阅读, 读者应该在需要时再回来查看. 因为这种章节只是一些枯燥引理及其证明的简单罗列, 而不包含动机的说明. 读者应该在使用这些引理的章节中寻找动机.

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.Syntax.SubstitutionFacts (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ

private variable
  n : ℕ
  σ τ : Subst
```

## 恒等替换

```agda
[id]ₜ : σ ≗ # → ∀ t → t [ σ ]ₜ ≡ t
[id]ₜ {σ} eq = term-elim eq H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → t [ σ ]ₜ ≡ t) → (f $̇ t⃗) [ σ ]ₜ ≡ (f $̇ t⃗)
  H f t⃗ IH rewrite []ₜ⃗≡map⃗ t⃗ σ = cong (f $̇_) $
    map⃗ (_[ σ ]ₜ) t⃗ ≡⟨ map⃗-ext IH ⟩
    map⃗ id t⃗        ≡⟨ map⃗-id t⃗ ⟩
    t⃗               ∎
```

```agda
[#]ₜ : t [ # ]ₜ ≡ t
[#]ₜ = [id]ₜ (λ _ → refl) _
```

```agda
↑ₛ-id : σ ≗ # → ↑ₛ σ ≗ #
↑ₛ-id eq zero = refl
↑ₛ-id eq (suc n) = cong ↑ₜ (eq n)
```

```agda
[id]ᵩ : σ ≗ # → ∀ φ → φ [ σ ]ᵩ ≡ φ
[id]ᵩ eq ⊥̇        = refl
[id]ᵩ eq (φ →̇ ψ)  = cong2 _→̇_ ([id]ᵩ eq φ) ([id]ᵩ eq ψ)
[id]ᵩ eq (∀̇ φ)    = cong ∀̇_ ([id]ᵩ (↑ₛ-id eq) φ)
[id]ᵩ {σ} eq (R $̇ t⃗) = cong (R $̇_) $
  map⃗ (_[ σ ]ₜ) t⃗ ≡⟨ map⃗-ext (λ t _ → [id]ₜ eq t) ⟩
  map⃗ id t⃗        ≡⟨ map⃗-id t⃗ ⟩
  t⃗               ∎
```

```agda
[#]ᵩ : φ [ # ]ᵩ ≡ φ
[#]ᵩ = [id]ᵩ (λ _ → refl) _
```

## 替换的复合

```agda
[]ₜ-∘-≗ : ∀ σ τ θ → _[ τ ]ₜ ∘ σ ≗ θ → _[ τ ]ₜ ∘ _[ σ ]ₜ ≗ _[ θ ]ₜ
[]ₜ-∘-≗ σ τ θ eq = term-elim (λ n → eq n) H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → t [ σ ]ₜ [ τ ]ₜ ≡ t [ θ ]ₜ) → (f $̇ t⃗) [ σ ]ₜ [ τ ]ₜ ≡ (f $̇ t⃗) [ θ ]ₜ
  H f t⃗ IH = cong (f $̇_) H2 where
    H2 : (t⃗ [ σ ]ₜ⃗) [ τ ]ₜ⃗ ≡ t⃗ [ θ ]ₜ⃗
    H2 rewrite []ₜ⃗≡map⃗ (t⃗ [ σ ]ₜ⃗) τ | []ₜ⃗≡map⃗ t⃗ σ | []ₜ⃗≡map⃗ t⃗ θ =
      map⃗ (_[ τ ]ₜ) (map⃗ (_[ σ ]ₜ) t⃗) ≡˘⟨ map⃗-∘ _ _ _ ⟩
      map⃗ (_[ τ ]ₜ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map⃗-ext IH ⟩
      map⃗ (_[ θ ]ₜ) t⃗                 ∎
```

```agda
[]ₜ-∘ : _[ τ ]ₜ ∘ _[ σ ]ₜ ≗ _[ _[ τ ]ₜ ∘ σ ]ₜ
[]ₜ-∘ = []ₜ-∘-≗ _ _ _ (λ _ → refl)
```

```agda
↑ₛ-∘-≗ : ∀ σ τ θ → _[ τ ]ₜ ∘ σ ≗ θ → _[ ↑ₛ τ ]ₜ ∘ ↑ₛ σ ≗ ↑ₛ θ
↑ₛ-∘-≗ σ τ θ eq zero = refl
↑ₛ-∘-≗ σ τ θ eq (suc n) =
  (_[ ↑ₛ τ ]ₜ ∘ ↑ₛ σ) (suc n)   ≡⟨⟩
  (σ n) [ # ∘ suc ]ₜ [ ↑ₛ τ ]ₜ  ≡⟨ []ₜ-∘ (σ n) ⟩
  (σ n) [ ↑ₜ ∘ τ ]ₜ             ≡˘⟨ []ₜ-∘ (σ n) ⟩
  (σ n) [ τ ]ₜ [ # ∘ suc ]ₜ     ≡⟨⟩
  ↑ₜ ((σ n) [ τ ]ₜ)             ≡⟨ cong ↑ₜ (eq n) ⟩
  ↑ₜ (θ n)                      ≡⟨⟩
  ↑ₛ θ (suc n)                  ∎
```

```agda
[]ᵩ-∘-≗ : ∀ σ τ θ → _[ τ ]ₜ ∘ σ ≗ θ → _[ τ ]ᵩ ∘ _[ σ ]ᵩ ≗ _[ θ ]ᵩ
[]ᵩ-∘-≗ σ τ θ eq ⊥̇       = refl
[]ᵩ-∘-≗ σ τ θ eq (φ →̇ ψ) = cong2 _→̇_ ([]ᵩ-∘-≗ σ τ θ eq φ) ([]ᵩ-∘-≗ σ τ θ eq ψ)
[]ᵩ-∘-≗ σ τ θ eq (∀̇ φ)   = cong ∀̇_ $ []ᵩ-∘-≗ (↑ₛ σ) (↑ₛ τ) (↑ₛ θ) (↑ₛ-∘-≗ σ τ θ eq) φ
[]ᵩ-∘-≗ σ τ θ eq (R $̇ t⃗) = cong (R $̇_) H where
  H = map⃗ (_[ τ ]ₜ) (map⃗ (_[ σ ]ₜ) t⃗) ≡˘⟨ map⃗-∘ _ _ _ ⟩
      map⃗ (_[ τ ]ₜ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map⃗-ext (λ t _ → []ₜ-∘-≗ _ _ _ eq t) ⟩
      map⃗ (_[ θ ]ₜ) t⃗                 ∎
```

```agda
[]ᵩ-∘ : _[ τ ]ᵩ ∘ _[ σ ]ᵩ ≗ _[ _[ τ ]ₜ ∘ σ ]ᵩ
[]ᵩ-∘ = []ᵩ-∘-≗ _ _ _ (λ _ → refl)
```

```agda
↑ᵩ[]₀ : (↑ᵩ φ) [ # n ]₀ ≡ φ
↑ᵩ[]₀ {φ} {n} =
  (↑ᵩ φ) [ # n ]₀                   ≡⟨ []ᵩ-∘ φ ⟩
  φ [ _[ # n ∷ₙ # ]ₜ ∘ # ∘ suc ]ᵩ   ≡⟨ [#]ᵩ ⟩
  φ                                 ∎
```

```agda
[]ᵩ∘[]₀ : _[ σ ]ᵩ ∘ _[ t ]₀ ≗ _[ t [ σ ]ₜ ]₀ ∘ _[ ↑ₛ σ ]ᵩ
[]ᵩ∘[]₀ {σ} {t} φ =
  φ [ t ]₀ [ σ ]ᵩ           ≡⟨ []ᵩ-∘ _ ⟩
  φ [ _[ σ ]ₜ ∘ (t ∷ₙ #) ]ᵩ ≡˘⟨ []ᵩ-∘-≗ (↑ₛ σ) (t [ σ ]ₜ ∷ₙ #) _ H φ ⟩
  φ [ ↑ₛ σ ]ᵩ [ t [ σ ]ₜ ]₀ ∎ where
    H : _[ t [ σ ]ₜ ∷ₙ # ]ₜ ∘ ↑ₛ σ ≗ _[ σ ]ₜ ∘ (t ∷ₙ #)
    H zero = refl
    H (suc n) =
      (σ n) [ # ∘ suc ]ₜ [ t [ σ ]ₜ ∷ₙ # ]ₜ     ≡⟨ []ₜ-∘ (σ n) ⟩
      (σ n) [ _[ t [ σ ]ₜ ∷ₙ # ]ₜ ∘ # ∘ suc ]ₜ  ≡⟨ [#]ₜ ⟩
      σ n                                       ∎
```

## 替换的外延性

```agda
[]ₜ-ext : σ ≗ τ → _[ σ ]ₜ ≗ _[ τ ]ₜ
[]ₜ-ext {σ} {τ} eq = term-elim eq H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → t [ σ ]ₜ ≡ t [ τ ]ₜ) → (f $̇ t⃗) [ σ ]ₜ ≡ (f $̇ t⃗) [ τ ]ₜ
  H f t⃗ IH = cong (f $̇_) H2 where
    H2 : t⃗ [ σ ]ₜ⃗ ≡ t⃗ [ τ ]ₜ⃗
    H2 rewrite []ₜ⃗≡map⃗ t⃗ σ | []ₜ⃗≡map⃗ t⃗ τ = map⃗-ext IH
```

```agda
↑ₛ-ext : σ ≗ τ → ↑ₛ σ ≗ ↑ₛ τ
↑ₛ-ext eq zero = refl
↑ₛ-ext eq (suc n) = cong ↑ₜ (eq n)
```

```agda
[]ᵩ-ext : σ ≗ τ → _[ σ ]ᵩ ≗ _[ τ ]ᵩ
[]ᵩ-ext eq ⊥̇        = refl
[]ᵩ-ext eq (φ →̇ ψ)  = cong2 _→̇_ ([]ᵩ-ext eq φ) ([]ᵩ-ext eq ψ)
[]ᵩ-ext eq (∀̇ φ)    = cong ∀̇_ ([]ᵩ-ext (↑ₛ-ext eq) φ)
[]ᵩ-ext eq (R $̇ t⃗)  = cong (R $̇_) (map⃗-ext λ t _ → []ₜ-ext eq t)
```

```agda
↑ᵩ∘[]ᵩ : ↑ᵩ ∘ _[ σ ]ᵩ ≗ _[ ↑ₛ σ ]ᵩ ∘ ↑ᵩ
↑ᵩ∘[]ᵩ {σ} φ =
  φ [ σ ]ᵩ [ # ∘ suc ]ᵩ       ≡⟨ []ᵩ-∘ _ ⟩
  φ [ _[ # ∘ suc ]ₜ ∘ σ ]ᵩ    ≡⟨ []ᵩ-ext (λ _ → refl) φ ⟩
  φ [ _[ ↑ₛ σ ]ₜ ∘ # ∘ suc ]ᵩ ≡˘⟨ []ᵩ-∘ _ ⟩
  φ [ # ∘ suc ]ᵩ [ ↑ₛ σ ]ᵩ    ∎
```

```agda
↑∘[] : ↑ (map (_[ σ ]ᵩ) Γ) ≡ map (_[ ↑ₛ σ ]ᵩ) (↑ Γ)
↑∘[] {σ} {Γ} =
  ↑ (map (_[ σ ]ᵩ) Γ)      ≡˘⟨ map-∘ Γ ⟩
  map (↑ᵩ ∘ _[ σ ]ᵩ) Γ     ≡⟨ map-ext (λ t _ → ↑ᵩ∘[]ᵩ t) ⟩
  map (_[ ↑ₛ σ ]ᵩ ∘ ↑ᵩ) Γ  ≡⟨ map-∘ Γ ⟩
  map (_[ ↑ₛ σ ]ᵩ) (↑ Γ)   ∎
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/SubstitutionFacts.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.SubstitutionFacts.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.substitution)  
> 交流Q群: 893531731
