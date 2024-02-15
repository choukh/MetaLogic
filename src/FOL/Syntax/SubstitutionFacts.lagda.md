---
url: fol.syntax.substitution
---

# 一阶逻辑 ▸ 语法 ▸ᐨ 替换的性质

这是一篇标题中带上标减号 (ᐨ) 的章节. 这表示这种章节不推荐线性阅读, 读者应该在需要时再回来查看. 因为这种章节只是一些枯燥引理的简单罗列, 而不包含动机的说明, 并且省去了大部分的自然语言证明. 读者应该在使用这些引理的章节中寻找动机, 并自行理解形式化的证明.

```agda
open import Foundation.Essential
open import FOL.Language.Base
module FOL.Syntax.SubstitutionFacts (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ

private variable
  n m : ℕ
  s : Term
  σ τ : Subst
```

## 恒等替换

**<u>引理</u>** 如果一个替换 `σ` 与 `#` 逐点相等, 那么它就是项的恒等替换.

```agda
[id]ₜ : σ ≗ # → ∀ t → t [ σ ]ₜ ≡ t
[id]ₜ {σ} eq = term-elim eq H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → t [ σ ]ₜ ≡ t) → (f $̇ t⃗) [ σ ]ₜ ≡ (f $̇ t⃗)
  H f t⃗ IH rewrite []ₜ⃗≡map⃗ t⃗ σ = cong (f $̇_) $
    map⃗ (_[ σ ]ₜ) t⃗ ≡⟨ map⃗-ext IH ⟩
    map⃗ id t⃗        ≡⟨ map⃗-id t⃗ ⟩
    t⃗               ∎
```

**<u>引理</u>** `#` 本身是项的恒等替换.

```agda
[#]ₜ : t [ # ]ₜ ≡ t
[#]ₜ = [id]ₜ (λ _ → refl) _
```

**<u>引理</u>** 替换的提升对恒等替换无效.

```agda
↑ₛ-id : σ ≗ # → ↑ₛ σ ≗ #
↑ₛ-id eq zero = refl
↑ₛ-id eq (suc n) = cong ↑ₜ (eq n)
```

**<u>引理</u>** 如果一个替换 `σ` 与 `#` 逐点相等, 那么它就是公式的恒等替换.

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

**<u>引理</u>** `#` 本身是公式的恒等替换.

```agda
[#]ᵩ : φ [ # ]ᵩ ≡ φ
[#]ᵩ = [id]ᵩ (λ _ → refl) _
```

## 替换的复合

**<u>引理</u>** 项替换的复合.

```agda
[]ₜ-∘-≗ : ∀ σ τ θ → _[ τ ]ₜ ∘ σ ≗ θ → _[ τ ]ₜ ∘ _[ σ ]ₜ ≗ _[ θ ]ₜ
[]ₜ-∘-≗ σ τ θ eq = term-elim (λ n → eq n) H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → t [ σ ]ₜ [ τ ]ₜ ≡ t [ θ ]ₜ) → (f $̇ t⃗) [ σ ]ₜ [ τ ]ₜ ≡ (f $̇ t⃗) [ θ ]ₜ
  H f t⃗ IH = cong (f $̇_) H₂ where
    H₂ : (t⃗ [ σ ]ₜ⃗) [ τ ]ₜ⃗ ≡ t⃗ [ θ ]ₜ⃗
    H₂ rewrite []ₜ⃗≡map⃗ (t⃗ [ σ ]ₜ⃗) τ | []ₜ⃗≡map⃗ t⃗ σ | []ₜ⃗≡map⃗ t⃗ θ =
      map⃗ (_[ τ ]ₜ) (map⃗ (_[ σ ]ₜ) t⃗) ≡˘⟨ map⃗-∘ _ _ _ ⟩
      map⃗ (_[ τ ]ₜ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map⃗-ext IH ⟩
      map⃗ (_[ θ ]ₜ) t⃗                 ∎

[]ₜ-∘ : _[ τ ]ₜ ∘ _[ σ ]ₜ ≗ _[ _[ τ ]ₜ ∘ σ ]ₜ
[]ₜ-∘ = []ₜ-∘-≗ _ _ _ (λ _ → refl)
```

**<u>引理</u>** 替换的复合的提升.

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

**<u>引理</u>** 公式替换的复合.

```agda
[]ᵩ-∘-≗ : ∀ σ τ θ → _[ τ ]ₜ ∘ σ ≗ θ → _[ τ ]ᵩ ∘ _[ σ ]ᵩ ≗ _[ θ ]ᵩ
[]ᵩ-∘-≗ σ τ θ eq ⊥̇       = refl
[]ᵩ-∘-≗ σ τ θ eq (φ →̇ ψ) = cong2 _→̇_ ([]ᵩ-∘-≗ σ τ θ eq φ) ([]ᵩ-∘-≗ σ τ θ eq ψ)
[]ᵩ-∘-≗ σ τ θ eq (∀̇ φ)   = cong ∀̇_ $ []ᵩ-∘-≗ (↑ₛ σ) (↑ₛ τ) (↑ₛ θ) (↑ₛ-∘-≗ σ τ θ eq) φ
[]ᵩ-∘-≗ σ τ θ eq (R $̇ t⃗) = cong (R $̇_) H where
  H = map⃗ (_[ τ ]ₜ) (map⃗ (_[ σ ]ₜ) t⃗) ≡˘⟨ map⃗-∘ _ _ _ ⟩
      map⃗ (_[ τ ]ₜ ∘ _[ σ ]ₜ) t⃗       ≡⟨ map⃗-ext (λ t _ → []ₜ-∘-≗ _ _ _ eq t) ⟩
      map⃗ (_[ θ ]ₜ) t⃗                 ∎

[]ᵩ-∘ : _[ τ ]ᵩ ∘ _[ σ ]ᵩ ≗ _[ _[ τ ]ₜ ∘ σ ]ᵩ
[]ᵩ-∘ = []ᵩ-∘-≗ _ _ _ (λ _ → refl)
```

**<u>引理</u>** 公式替换与公式应用的复合.

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

**<u>引理</u>** 公式提升后的任意应用都等于原公式.

```agda
↑[]₀ : (↑ φ) [ t ]₀ ≡ φ
↑[]₀ {φ} {t} =
  (↑ φ) [ t ]₀                  ≡⟨ []ᵩ-∘ φ ⟩
  φ [ _[ t ∷ₙ # ]ₜ ∘ # ∘ suc ]ᵩ ≡⟨ [#]ᵩ ⟩
  φ                             ∎
```

类似地, 对项有

**<u>引理</u>** 项提升后的任意“应用”都等于原项.

```agda
↑ₜ[]₀ : (↑ₜ t) [ s ∷ₙ # ]ₜ ≡ t
↑ₜ[]₀ {t} {s} =
  (↑ₜ t) [ s ∷ₙ # ]ₜ            ≡⟨ []ₜ-∘ t ⟩
  t [ _[ s ∷ₙ # ]ₜ ∘ # ∘ suc ]ₜ ≡⟨ [#]ₜ ⟩
  t                             ∎
```

## 替换的外延性

**<u>引理</u>** 项替换的外延性: 如果 `σ` 与 `τ` 逐点相等, 那么 `_[ σ ]ₜ` 与 `_[ τ ]ₜ` 逐点相等.

```agda
[]ₜ-ext : σ ≗ τ → _[ σ ]ₜ ≗ _[ τ ]ₜ
[]ₜ-ext {σ} {τ} eq = term-elim eq H where
  H : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → t [ σ ]ₜ ≡ t [ τ ]ₜ) → (f $̇ t⃗) [ σ ]ₜ ≡ (f $̇ t⃗) [ τ ]ₜ
  H f t⃗ IH = cong (f $̇_) H₂ where
    H₂ : t⃗ [ σ ]ₜ⃗ ≡ t⃗ [ τ ]ₜ⃗
    H₂ rewrite []ₜ⃗≡map⃗ t⃗ σ | []ₜ⃗≡map⃗ t⃗ τ = map⃗-ext IH
```

**<u>引理</u>** 替换的提升尊重替换的逐点相等.

```agda
↑ₛ-ext : σ ≗ τ → ↑ₛ σ ≗ ↑ₛ τ
↑ₛ-ext eq zero = refl
↑ₛ-ext eq (suc n) = cong ↑ₜ (eq n)
```

**<u>引理</u>** 公式替换的外延性: 如果 `σ` 与 `τ` 逐点相等, 那么 `_[ σ ]ᵩ` 与 `_[ τ ]ᵩ` 逐点相等.

```agda
[]ᵩ-ext : σ ≗ τ → _[ σ ]ᵩ ≗ _[ τ ]ᵩ
[]ᵩ-ext eq ⊥̇        = refl
[]ᵩ-ext eq (φ →̇ ψ)  = cong2 _→̇_ ([]ᵩ-ext eq φ) ([]ᵩ-ext eq ψ)
[]ᵩ-ext eq (∀̇ φ)    = cong ∀̇_ ([]ᵩ-ext (↑ₛ-ext eq) φ)
[]ᵩ-ext eq (R $̇ t⃗)  = cong (R $̇_) (map⃗-ext λ t _ → []ₜ-ext eq t)
```

**<u>引理</u>** 公式替换与提升的复合.

```agda
↑∘[]ᵩ : ↑_ ∘ _[ σ ]ᵩ ≗ _[ ↑ₛ σ ]ᵩ ∘ ↑_
↑∘[]ᵩ {σ} φ =
  φ [ σ ]ᵩ [ # ∘ suc ]ᵩ       ≡⟨ []ᵩ-∘ _ ⟩
  φ [ _[ # ∘ suc ]ₜ ∘ σ ]ᵩ    ≡⟨ []ᵩ-ext (λ _ → refl) φ ⟩
  φ [ _[ ↑ₛ σ ]ₜ ∘ # ∘ suc ]ᵩ ≡˘⟨ []ᵩ-∘ _ ⟩
  φ [ # ∘ suc ]ᵩ [ ↑ₛ σ ]ᵩ    ∎
```

**<u>引理</u>** 语境替换与提升的复合.

```agda
↑∘[] : ⇞ (map (_[ σ ]ᵩ) Γ) ≡ map (_[ ↑ₛ σ ]ᵩ) (⇞ Γ)
↑∘[] {σ} {Γ} =
  ⇞ (map (_[ σ ]ᵩ) Γ)      ≡˘⟨ map-∘ Γ ⟩
  map (↑_ ∘ _[ σ ]ᵩ) Γ     ≡⟨ map-ext (λ t _ → ↑∘[]ᵩ t) ⟩
  map (_[ ↑ₛ σ ]ᵩ ∘ ↑_) Γ  ≡⟨ map-∘ Γ ⟩
  map (_[ ↑ₛ σ ]ᵩ) (⇞ Γ)   ∎
```

**<u>引理</u>** 公式恒等替换的一个实例.

```agda
↑ₛ[]₀ : φ [ ↑ₛ (# ∘ suc) ]ᵩ [ # 0 ]₀ ≡ φ
↑ₛ[]₀ {φ} = []ᵩ-∘ φ ∙ (sym $ []ᵩ-ext H φ) ∙ [#]ᵩ where
  H : # ≗ _[ # 0 ∷ₙ # ]ₜ ∘ (↑ₛ (# ∘ suc))
  H zero = refl
  H (suc n) = refl
```

**<u>引理</u>** 公式应用与公式替换的一种复合.

```agda
[]₀∘[↑]ᵩ : _[ t ]₀ ∘ _[ ↑ₛ σ ]ᵩ ≗ _[ t ∷ₙ σ ]ᵩ
[]₀∘[↑]ᵩ {t} {σ} φ =
  φ [ ↑ₛ σ ]ᵩ [ t ]₀          ≡⟨ []ᵩ-∘ φ ⟩
  φ [ _[ t ∷ₙ # ]ₜ ∘ ↑ₛ σ ]ᵩ  ≡˘⟨ []ᵩ-ext eq φ ⟩
  φ [ t ∷ₙ σ ]ᵩ               ∎
  where
  eq : t ∷ₙ σ ≗ _[ t ∷ₙ # ]ₜ ∘ ↑ₛ σ
  eq zero = refl
  eq (suc n) = sym ↑ₜ[]₀
```

## 含新变元的替换

**<u>引理</u>** 如果对任意 `n`, 要么 `n` 是 `t` 的新变元, 要么 `σ` 与 `τ` 在该处取值相等, 那么 `t [ σ ]ₜ ≡ t [ τ ]ₜ`.

```agda
[]ₜ-ext-freshₜ-dec : Decℙ P → (∀ n → ¬ P n → σ n ≡ τ n) →
  ∀ t → (∀ n → P n → freshₜ n t) → t [ σ ]ₜ ≡ t [ τ ]ₜ
[]ₜ-ext-freshₜ-dec {P} {σ} {τ} decP Hext = term-elim H# H$̇ where
  H# : ∀ m → (∀ n → P n → freshₜ n (# m)) → # m [ σ ]ₜ ≡ # m [ τ ]ₜ
  H# m Hfresh with decP m
  ... | no ¬Pm = Hext m ¬Pm
  ... | yes Pm = exfalso $ fresh#-elim (Hfresh m Pm) refl
  H$̇ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → (∀ n → P n → freshₜ n t) → t [ σ ]ₜ ≡ t [ τ ]ₜ) →
    (∀ n → P n → freshₜ n (f $̇ t⃗)) → (f $̇ t⃗) [ σ ]ₜ ≡ (f $̇ t⃗) [ τ ]ₜ
  H$̇ f t⃗ IH Hfresh rewrite []ₜ⃗≡map⃗ t⃗ σ | []ₜ⃗≡map⃗ t⃗ τ = cong (f $̇_) $ map⃗-ext
    λ t t∈⃗ → IH t t∈⃗ λ n Pn → fresh$̇-elim (Hfresh n Pn) t t∈⃗
```

**<u>引理</u>** 如果对任意 `n`, 要么 `n` 是 `φ` 的新变元, 要么 `σ` 与 `τ` 在该处取值相等, 那么 `φ [ σ ]ᵩ ≡ φ [ τ ]ᵩ`.

```agda
[]ᵩ-ext-freshᵩ-dec : Decℙ P → (∀ n → ¬ P n → σ n ≡ τ n) →
  ∀ φ → (∀ n → P n → freshᵩ n φ) → φ [ σ ]ᵩ ≡ φ [ τ ]ᵩ
[]ᵩ-ext-freshᵩ-dec _ _ ⊥̇ _ = refl
[]ᵩ-ext-freshᵩ-dec decP Hext (R $̇ t⃗) Hfresh = cong (R $̇_) $ map⃗-ext
  λ t t∈⃗ → []ₜ-ext-freshₜ-dec decP Hext t λ n Pn → freshR$̇-elim (Hfresh n Pn) t t∈⃗
[]ᵩ-ext-freshᵩ-dec {P} decP Hext (φ →̇ ψ) Hfresh = cong2 _→̇_
  ([]ᵩ-ext-freshᵩ-dec decP Hext φ λ n Pn → fst $ fresh→̇-elim $ Hfresh n Pn)
  ([]ᵩ-ext-freshᵩ-dec decP Hext ψ λ n Pn → snd $ fresh→̇-elim $ Hfresh n Pn)
[]ᵩ-ext-freshᵩ-dec {P} {σ} {τ} decP Hext (∀̇ φ) Hfresh = cong ∀̇_ $
  []ᵩ-ext-freshᵩ-dec {P = P′} H₁ H₂ φ H₃ where
  P′ : ℕ → 𝕋 _
  P′ zero = ⊥*
  P′ (suc n) = P n
  H₁ : Decℙ P′
  H₁ zero = no λ ()
  H₁ (suc n) = decP n
  H₂ : ∀ n → ¬ P′ n → ↑ₛ σ n ≡ ↑ₛ τ n
  H₂ zero _ = refl
  H₂ (suc n) ¬Pn = (cong (_[ # ∘ suc ]ₜ)) (Hext n ¬Pn)
  H₃ : ∀ n → P′ n → freshᵩ n φ
  H₃ (suc n) Pn = fresh∀̇-elim (Hfresh n Pn)
```

**<u>引理</u>** 如果 `n` 是 `φ` 的新变元, 且 `σ` 与 `τ` 在 `n` 之外逐点相等, 那么 `φ [ σ ]ᵩ ≡ φ [ τ ]ᵩ`.

```agda
[]ᵩ-ext-freshᵩ : freshᵩ n φ → (∀ m → m ≢ n → σ m ≡ τ m) → φ [ σ ]ᵩ ≡ φ [ τ ]ᵩ
[]ᵩ-ext-freshᵩ {n} {φ} Hfresh Hext = []ᵩ-ext-freshᵩ-dec {P = _≡ n} (λ _ → it) Hext φ λ { _ refl → Hfresh }
```

**<u>引理</u>** 如果对任意 `n : ℕ` 要么 `n` 是 `t` 的新变元要么 `m` 是 `σ n` 的新变元, 那么 `m` 是 `t [ σ ]ₜ` 的新变元.

```agda
fresh[]ₜ : ∀ t → (∀ n → freshₜ n t ⊎ freshₜ m (σ n)) → freshₜ m (t [ σ ]ₜ)
fresh[]ₜ {m} {σ} = term-elim H₁ H₂ where
  H₁ : ∀ k → (∀ n → freshₜ n (# k) ⊎ freshₜ m (σ n)) → freshₜ m (# k [ σ ]ₜ)
  H₁ k H with H k
  ... | inj₁ (fresh# k≢k) = exfalso (k≢k refl)
  ... | inj₂ H = H
  H₂ : ∀ f t⃗ → (∀ t → t ∈⃗ t⃗ → (∀ n → freshₜ n t ⊎ freshₜ m (σ n)) → freshₜ m (t [ σ ]ₜ)) →
      (∀ n → freshₜ n (f $̇ t⃗) ⊎ freshₜ m (σ n)) → freshₜ m ((f $̇ t⃗) [ σ ]ₜ)
  H₂ f t⃗ IH H rewrite []ₜ⃗≡map⃗ t⃗ σ = fresh$̇ (map⃗⊆P H₃) where
    H₃ : ∀ t → t ∈⃗ t⃗ → freshₜ m (t [ σ ]ₜ)
    H₃ t t∈⃗ = IH t t∈⃗ H₄ where
      H₄ : ∀ n → freshₜ n t ⊎ freshₜ m (σ n)
      H₄ n with H n
      ... | inj₁ (fresh$̇ H) = inj₁ (H t t∈⃗)
      ... | inj₂ H = inj₂ H
```

**<u>引理</u>** 如果对任意 `n : ℕ` 要么 `n` 是 `φ` 的新变元要么 `m` 是 `σ n` 的新变元, 那么 `m` 是 `φ [ σ ]ᵩ` 的新变元.

```agda
fresh[]ᵩ : (∀ n → freshᵩ n φ ⊎ freshₜ m (σ n)) → freshᵩ m (φ [ σ ]ᵩ)
fresh[]ᵩ {(⊥̇)} H = fresh⊥̇
fresh[]ᵩ {φ →̇ ψ} {m} {σ} H = fresh→̇ (fresh[]ᵩ H₁) (fresh[]ᵩ H₂) where
  H₁ : ∀ n → freshᵩ n φ ⊎ freshₜ m (σ n)
  H₁ n with H n
  ... | inj₁ (fresh→̇ H _) = inj₁ H
  ... | inj₂ H = inj₂ H
  H₂ : ∀ n → freshᵩ n ψ ⊎ freshₜ m (σ n)
  H₂ n with H n
  ... | inj₁ (fresh→̇ _ H) = inj₁ H
  ... | inj₂ H = inj₂ H
fresh[]ᵩ {∀̇ φ} {m} {σ} H = fresh∀̇ (fresh[]ᵩ H₁) where
  H₁ : ∀ n → freshᵩ n φ ⊎ freshₜ (suc m) (↑ₛ σ n)
  H₁ zero = inj₂ $ fresh# λ ()
  H₁ (suc n) with H n
  ... | inj₁ (fresh∀̇ H) = inj₁ H
  ... | inj₂ H = inj₂ $ fresh[]ₜ (σ n) H₂ where
    H₂ : ∀ k → freshₜ k (σ n) ⊎ freshₜ (suc m) (# (suc k))
    H₂ k with k ≟ m
    ... | yes refl = inj₁ H
    ... | no k≢m = inj₂ $ fresh# λ { refl → exfalso (k≢m refl)}
fresh[]ᵩ {R $̇ t⃗} {m} {σ} H = fresh$̇ (map⃗⊆P H₁) where
  H₁ : ∀ t → t ∈⃗ t⃗ → freshₜ m (t [ σ ]ₜ)
  H₁ t t∈⃗ = fresh[]ₜ t H₂ where
    H₂ : ∀ n → freshₜ n t ⊎ freshₜ m (σ n)
    H₂ n with H n
    ... | inj₁ (fresh$̇ H) = inj₁ (H t t∈⃗)
    ... | inj₂ H = inj₂ H
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/SubstitutionFacts.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.SubstitutionFacts.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.substitution)  
> 交流Q群: 893531731
 