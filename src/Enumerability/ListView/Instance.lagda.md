---
url: foundation.enumerability.listview.instance
---

# 可枚举性 ▸ 累积列表视角 ▸ 实例

```agda
{-# OPTIONS --lossy-unification #-}
module Enumerability.ListView.Instance where
open import Enumerability.ListView.Base

open import Foundation.Essential
  hiding (_∈_) renaming (_∈ᴸ_ to _∈_)
open import Foundation.Data.Nat.AlternativeOrder

private variable
  m n o : ℕ

instance
  enum𝔹 : Enum 𝔹
  enum𝔹 = mkEnum (λ _ → true ∷ [ false ]) (λ n → [] , refl)
    λ { true →  ex 0 $ here refl
      ; false → ex 0 $ there (here refl) }

  enumℕ : Enum ℕ
  enumℕ = mkEnum e c w where
    e : 𝕃ₙ ℕ
    e zero = [ 0 ]
    e (suc n) = e n ++ [ suc n ]
    c : Cumulation e
    c _ = _ , refl
    w : ∀ n → e witness n
    w n = ex n (H n) where
      H : ∀ n → n ∈ e n
      H zero = here refl
      H (suc n) = ∈-++⁺ʳ (here refl)

  enum× : ⦃ Enum A ⦄ → ⦃ Enum B ⦄ → Enum (A × B)
  enum× {A} {B} = mkEnum e c w where
    e : 𝕃ₙ (A × B)
    e zero = enum 0 [×] enum 0
    e (suc n) = e n ++ enum n [×] enum n
    c : Cumulation e
    c n = enum n [×] enum n , refl
    w : ∀ xy → e witness xy
    w (x , y) = 𝟙.map2 H (wit x) (wit y) where
      H : Witness enum x → Witness enum y → Witness e (x , y)
      H (m , x∈fm) (n , x∈gn) = suc (m + n) , ∈-++⁺ʳ H2 where
        H2 : (x , y) ∈ enum (m + n) [×] enum (m + n)
        H2 = ∈[×]-intro (cum-≤→⊆ cum m≤m+n x∈fm) (cum-≤→⊆ cum m≤n+m x∈gn)

  enumVec : ⦃ Enum A ⦄ → Enum (𝕍 A n)
  enumVec {A} = mkEnum e c w where

    e : 𝕃ₙ (𝕍 A n)
    e zero = []
    e {n} (suc m) = e m ++ combine (enum m) n

    c : Cumulation e
    c _ = _ , refl

    e-≤→⊆ : {x⃗ : 𝕍 A n} → m ≤ o → x⃗ ∈ e m → x⃗ ∈ combine (enum o) n
    e-≤→⊆ {m = suc m} sm≤o H with ∈-++⁻ (e m) H
    ... | inj₁ x⃗∈en   = e-≤→⊆ (m+n≤o⇒n≤o 1 sm≤o) x⃗∈en
    ... | inj₂ x⃗∈comb = combine-≤→⊆ cum (m+n≤o⇒n≤o 1 sm≤o) x⃗∈comb

    w : (x⃗ : 𝕍 A n) → e witness x⃗
    w [] = ex 1 (here refl)
    w (x ∷ x⃗) = 𝟙.map2 H (wit x) (w x⃗) where
      H : Witness enum x → Witness e x⃗ → Witness e (x ∷ x⃗)
      H (m , Hm) (suc n , Hn) = suc m + suc n , ∈-++⁺ʳ (∈map[×]-intro H1 H2) where
        H1 : x ∈ enum (m + suc n)
        H1 = cum-≤→⊆ cum m≤m+n Hm
        H2 : x⃗ ∈ combine (enum (m + suc n)) _
        H2 = e-≤→⊆ m≤n+m Hn
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Enumerability/ListView/Instance.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Enumerability.ListView.Instance.html) | [语雀](https://www.yuque.com/ocau/metalogic/enumerability.listview.instance)  
> 交流Q群: 893531731
