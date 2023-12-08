{-# OPTIONS --lossy-unification #-}

open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder

module Enumerability.ListView.Combine where
open import Enumerability.ListView.Base

private variable
  f : 𝕃ₙ A
  m n o : ℕ

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
      H1 : x ∈ᴸ f (m + o)
      H1 = cum-≤→⊆ cum m≤m+n Hm
      H2 : x⃗ ∈ᴸ combine (f (m + o)) _
      H2 = combine-≤→⊆ cum m≤n+m Ho
