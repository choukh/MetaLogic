open import Foundation.Essential
  hiding (_∈_) renaming (_∈ᴸ_ to _∈_)
open import Foundation.Data.Nat.AlternativeOrder

module Enumerability.ListView.Base where

𝕃ₙ : 𝕋 ℓ → 𝕋 ℓ
𝕃ₙ A = ℕ → 𝕃 A

Cumulation : 𝕃ₙ A → 𝕋 _
Cumulation f = ∀ n → Σ xs ， f (suc n) ≡ f n ++ xs

module _ {f : 𝕃ₙ A} (cum : Cumulation f) where

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
