module Foundation.Data.List.Cumulation where

open import Foundation.Prelude
open import Foundation.Data.Nat
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic
open import Foundation.Data.Sigma

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
