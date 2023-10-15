module Foundation.Data.List.Cumulative where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Data.Nat
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.Sigma

open import Foundation.Data.List.SetTheoretic public

𝕃ₙ : 𝕋 ℓ → 𝕋 ℓ
𝕃ₙ A = ℕ → 𝕃 A

cumulative : 𝕃ₙ A → 𝕋 _
cumulative f = ∀ n → ∃ xs ⸴ f (suc n) ＝ f n ++ xs

module _ {f : 𝕃ₙ A} (cum : cumulative f) where

  cum-≤→++ : (m n : ℕ) → m ≤ n → ∃ xs ⸴ f n ＝ f m ++ xs
  cum-≤→++ n n ≤-refl = exists [] (sym $ ++-identityʳ (f n))
  cum-≤→++ m (suc n) (≤-step m≤n) = intro₁2 (cum n) (cum-≤→++ m n m≤n)
    λ (xs , H₁) (ys , H₂) → (ys ++ xs) ,
      f (suc n)         ＝⟨ H₁ ⟩
      f n ++ xs         ＝⟨ cong (_++ xs) H₂ ⟩
      (f m ++ ys) ++ xs ＝⟨ ++-assoc (f m) ys xs ⟩
      f m ++ ys ++ xs   ∎

  cum-≤→⊆ : (m n : ℕ) → m ≤ n → ∥ f m ⊆ f n ∥₁
  cum-≤→⊆ m n m≤n = intro₁ (cum-≤→++ m n m≤n)
    λ (xs , eq) x∈fm → subst (_ ∈_) eq (∈-++⁺ˡ x∈fm)
