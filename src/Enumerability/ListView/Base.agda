{-# OPTIONS --lossy-unification #-}
module Enumerability.ListView.Base where

open import Foundation.Essential
  hiding (_∈_) renaming (_∈ᴸ_ to _∈_)
open import Foundation.Data.Nat.AlternativeOrder

𝕃ₙ : 𝕋 ℓ → 𝕋 ℓ
𝕃ₙ A = ℕ → 𝕃 A

private variable
  f : 𝕃ₙ A
  m n o : ℕ

Cumulation : 𝕃ₙ A → 𝕋 _
Cumulation f = ∀ n → Σ xs ， f (suc n) ≡ f n ++ xs

module _ (cum : Cumulation f) where

  cum-≤→++ : {m n : ℕ} → m ≤ n → Σ xs ， f n ≡ f m ++ xs
  cum-≤→++ {m = n} {n} ≤-refl = [] , sym (++-identityʳ (f n))
  cum-≤→++ {m} {suc n} (≤-step m≤n) with cum n | cum-≤→++ m≤n
  ... | xs , H₁ | ys , H₂ = (ys ++ xs) ,
    f (suc n)         ≡⟨ H₁ ⟩
    f n ++ xs         ≡⟨ cong (_++ xs) H₂ ⟩
    (f m ++ ys) ++ xs ≡⟨ ++-assoc (f m) ys xs ⟩
    f m ++ ys ++ xs   ∎

  cum-≤→⊆ : {m n : ℕ} → m ≤ n → f m ⊆ f n
  cum-≤→⊆ m≤n x∈fm with cum-≤→++ m≤n
  ... | xs , eq = subst (_ ∈_) eq (∈-++⁺ˡ x∈fm)

Witness : 𝕃ₙ A → A → 𝕋 _
Witness f x = Σ n ， x ∈ f n

_witness_ : 𝕃ₙ A → A → 𝕋 _
f witness x = ∥ Witness f x ∥₁

record Enum (A : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  constructor mkEnum
  field
    enum : 𝕃ₙ A
    cum : Cumulation enum
    wit : ∀ x → enum witness x

record Enumℙ {A : 𝕋 ℓ} (P : A → 𝕋 ℓ′) : 𝕋 (ℓ ⊔ ℓ′) where
  constructor mkEnumℙ
  field
    enumℙ : 𝕃ₙ A
    cumℙ : Cumulation enumℙ
    witℙ : ∀ x → P x ↔ enumℙ witness x

open Enum ⦃...⦄ public
open Enumℙ ⦃...⦄ public

Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
Enum↔ℙ = ⇒: (λ (mkEnum f cum H) → mkEnumℙ f cum λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
          ⇐: (λ (mkEnumℙ f cum H) → mkEnum f cum λ x → H x .⇒ tt)

enumerable : 𝕋 ℓ → 𝕋 _
enumerable A = ∥ Enum A ∥₁

enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
enumerableℙ P = ∥ Enumℙ P ∥₁

enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
enumerable↔ℙ = ↔-map Enum↔ℙ

combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (uncurry _∷_) (xs [×] combine xs n)

combine-≤→⊆ : Cumulation f → m ≤ o → combine (f m) n ⊆ combine (f o) n
combine-≤→⊆ {n = zero} _ _ H = H
combine-≤→⊆ {n = suc n} cum m≤o H with ∈map[×]-elim H
... | x , y , x∈ , y∈ , refl = ∈map[×]-intro (cum-≤→⊆ cum m≤o x∈) (combine-≤→⊆ cum m≤o y∈)

combine-wit : Cumulation f → (x⃗ : 𝕍 A n) →
  (∀ x → x ∈⃗ x⃗ → f witness x) → (λ k → combine (f k) n) witness x⃗
combine-wit _ [] _ = ex 0 (here refl)
combine-wit {f} cum (x ∷ x⃗) H0 = 𝟙.map2 H (H0 x (here refl)) IH where
    IH = combine-wit cum x⃗ λ y y∈⃗ → H0 y (there y∈⃗)
    H : Witness f x → Witness _ x⃗ → Witness _ (x ∷ x⃗)
    H (m , Hm) (o , Ho) = m + o , ∈map[×]-intro H1 H2 where
      H1 : x ∈ f (m + o)
      H1 = cum-≤→⊆ cum m≤m+n Hm
      H2 : x⃗ ∈ combine (f (m + o)) _
      H2 = combine-≤→⊆ cum m≤n+m Ho
