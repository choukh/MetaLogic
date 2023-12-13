---
url: foundation.enumeration.listview.base
---

# 元语言 ▸ 可枚举性 ▸ 累积列表视角 ▸ 定义

本章介绍枚举的第2种视角.

```agda
{-# OPTIONS --lossy-unification #-}
module Foundation.Function.Enumeration.ListView.Base where

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Sum
open import Foundation.Data.Sigma
```

我们需要同时谈论列表的 `_∈_` 和向量的 `_∈_`, 分别记作 `_∈ᴸ_` 和 `_∈⃗_`, 以示区别.

```agda
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic
  renaming (_∈_ to _∈ᴸ_)
open import Foundation.Data.Vec
open import Foundation.Data.Vec.SetTheoretic
  renaming (_∈_ to _∈⃗_)
```

## 累积列表

**<u>定义</u>** 给定 `A`, 我们把列表 `𝕃 A` 的无穷序列记作 `𝕃ₙ A`.

```agda
𝕃ₙ : 𝕋 ℓ → 𝕋 ℓ
𝕃ₙ A = ℕ → 𝕃 A
```

**<u>约定</u>** 本章使用 `f` 表示某 `A` 的列表的无穷序列, `m` `n` `o` 表示自然数.

```agda
private variable
  f : 𝕃ₙ A
  m n o : ℕ
```

**<u>定义</u>** 列表的无穷序列 `f : 𝕃ₙ A` 的一个累积, 记作 `Cumulation f`, 是一个以 `n : ℕ` 为索引的集族, 对每个 `n` 都给出了一个 `xs : 𝕃 A`, 使得 `f n ≡ f m ++ xs` 成立. 其中 `_++_` 是列表的拼接操作.

```agda
Cumulation : 𝕃ₙ A → 𝕋 _
Cumulation f = ∀ n → Σ xs ， f (suc n) ≡ f n ++ xs
```

```agda
module _ (cum : Cumulation f) where
  cum-≤→++ : m ≤ n → Σ xs ， f n ≡ f m ++ xs
  cum-≤→++ {m = n} {n} ≤-refl = [] , sym (++-identityʳ (f n))
  cum-≤→++ {m} {suc n} (≤-step m≤n) with cum n | cum-≤→++ m≤n
  ... | xs , H₁ | ys , H₂ = (ys ++ xs) ,
    f (suc n)         ≡⟨ H₁ ⟩
    f n ++ xs         ≡⟨ cong (_++ xs) H₂ ⟩
    (f m ++ ys) ++ xs ≡⟨ ++-assoc (f m) ys xs ⟩
    f m ++ ys ++ xs   ∎
```

```agda
  cum-≤→⊆ : m ≤ n → f m ⊆ f n
  cum-≤→⊆ m≤n x∈fm with cum-≤→++ m≤n
  ... | xs , eq = subst (_ ∈ᴸ_) eq (∈-++⁺ˡ x∈fm)
```

```agda
  cum-length : m ≤ n → length (f m) ≤ length (f n)
  cum-length {m} {n} m≤n with cum-≤→++ m≤n
  ... | xs , eq = subst (_ ≤_) H m≤m+n where
    H = length (f n)              ≡⟨ cong length eq ⟩
        length (f m ++ xs)        ≡⟨ length-++ _ ⟩
        length (f m) + length xs  ∎
```

```agda
  cum-≤→Σ : m ≤ n → Σ xs ， f n ≡ f m ++ xs
  cum-≤→Σ ≤-refl = [] , (sym $ ++-identityʳ _)
  cum-≤→Σ (≤-step {n} m≤n) with cum-≤→Σ m≤n | cum n
  ... | xs , Hx | ys , Hy rewrite Hy | Hx = xs ++ ys , ++-assoc _ _ _
```

```agda
  cum-total : ∀ m n → (Σ xs ， f n ≡ f m ++ xs) ⊎ (Σ xs ， f m ≡ f n ++ xs) 
  cum-total m n with ≤-total m n
  ... | inj₁ m≤n = inj₁ (cum-≤→Σ m≤n)
  ... | inj₂ n≤m = inj₂ (cum-≤→Σ n≤m)
```

## 枚举的定义

```agda
Witness : 𝕃ₙ A → A → 𝕋 _
Witness f x = Σ n ， x ∈ᴸ f n
```

```agda
_witness_ : 𝕃ₙ A → A → 𝕋 _
f witness x = ∥ Witness f x ∥₁
```

```agda
record Enum (A : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  constructor mkEnum
  field
    enum : 𝕃ₙ A
    cum : Cumulation enum
    wit : ∀ x → enum witness x
```

```agda
record Enumℙ {A : 𝕋 ℓ} (P : A → 𝕋 ℓ′) : 𝕋 (ℓ ⊔ ℓ′) where
  constructor mkEnumℙ
  field
    enumℙ : 𝕃ₙ A
    cumℙ : Cumulation enumℙ
    witℙ : ∀ x → P x ↔ enumℙ witness x
```

```agda
open Enum ⦃...⦄ public
open Enumℙ ⦃...⦄ public
```

```agda
Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
Enum↔ℙ = ⇒: (λ (mkEnum f cum H) → mkEnumℙ f cum λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
          ⇐: (λ (mkEnumℙ f cum H) → mkEnum f cum λ x → H x .⇒ tt)
```

```agda
enumerable : 𝕋 ℓ → 𝕋 _
enumerable A = ∥ Enum A ∥₁
```

```agda
enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
enumerableℙ P = ∥ Enumℙ P ∥₁
```

```agda
enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
enumerable↔ℙ = ↔-map Enum↔ℙ
```

## 列表元素的组合

```agda
combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (uncurry _∷_) (xs [×] combine xs n)
```

```agda
combine-≤→⊆ : Cumulation f → m ≤ o → combine (f m) n ⊆ combine (f o) n
combine-≤→⊆ {n = zero} _ _ H = H
combine-≤→⊆ {n = suc n} cum m≤o H with ∈map[×]-elim H
... | x , y , x∈ , y∈ , refl = ∈map[×]-intro (cum-≤→⊆ cum m≤o x∈) (combine-≤→⊆ cum m≤o y∈)
```

```agda
combine-wit : Cumulation f → (x⃗ : 𝕍 A n) →
  (∀ x → x ∈⃗ x⃗ → f witness x) → (λ k → combine (f k) n) witness x⃗
combine-wit _ [] _ = ex 0 (here refl)
combine-wit {f} cum (x ∷ x⃗) H0 = 𝟙.map2 H (H0 x (here refl)) IH where
    IH = combine-wit cum x⃗ λ y y∈⃗ → H0 y (there y∈⃗)
    H : Witness f x → Witness _ x⃗ → Witness _ (x ∷ x⃗)
    H (m , Hm) (o , Ho) = m + o , ∈map[×]-intro H1 H2 where
      H1 : x ∈ᴸ f (m + o)
      H1 = cum-≤→⊆ cum m≤m+n Hm
      H2 : x⃗ ∈ᴸ combine (f (m + o)) _
      H2 = combine-≤→⊆ cum m≤n+m Ho
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/ListView/Base.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Function.Enumeration.ListView.Base.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.enumeration.listview.base)  
> 交流Q群: 893531731
