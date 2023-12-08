{-# OPTIONS --lossy-unification #-}

open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder
open import Enumerability.View.Lists
open import Enumerability.Combine

module Enumerability.Instance where

private variable
  m n o : ℕ

instance
  enumVec : ⦃ Enum A ⦄ → Enum (𝕍 A n)
  enumVec {A} = mkEnum e c w where

    e : 𝕃ₙ (𝕍 A n)
    e zero = []
    e {n} (suc m) = e m ++ combine (enum m) n

    c : Cumulation e
    c _ = _ , refl

    e-≤→⊆ : {x⃗ : 𝕍 A n} → m ≤ o → x⃗ ∈ᴸ e m → x⃗ ∈ᴸ combine (enum o) n
    e-≤→⊆ {m = suc m} sm≤o H with ∈-++⁻ (e m) H
    ... | inj₁ x⃗∈en   = e-≤→⊆ (m+n≤o⇒n≤o 1 sm≤o) x⃗∈en
    ... | inj₂ x⃗∈comb = combine-≤→⊆ cum (m+n≤o⇒n≤o 1 sm≤o) x⃗∈comb

    w : (x⃗ : 𝕍 A n) → e witness x⃗
    w [] = ex 1 (here refl)
    w (x ∷ x⃗) = 𝟙.map2 H (wit x) (w x⃗) where
      H : Witness enum x → Witness e x⃗ → Witness e (x ∷ x⃗)
      H (m , Hm) (suc n , Hn) = suc m + suc n , ∈-++⁺ʳ (∈map[×]-intro H1 H2) where
        H1 : x ∈ᴸ enum (m + suc n)
        H1 = cum-≤→⊆ cum m≤m+n Hm
        H2 : x⃗ ∈ᴸ combine (enum (m + suc n)) _
        H2 = e-≤→⊆ m≤n+m Hn
