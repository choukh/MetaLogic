{-# OPTIONS --lossy-unification #-}
module Foundation.Function.Enumeration.ListView.Properties where
open import Foundation.Function.Enumeration.ListView.Base
open import Foundation.Function.Enumeration.ListView.Instance
import Foundation.Function.Enumeration.MaybeView as Ⓜ

open import Foundation.Prelude
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation

open import Foundation.Data.Maybe
open import Foundation.Data.Nat
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Sigma
open import Foundation.Data.Sum
open import Foundation.Data.List
open import Foundation.Data.List.SetTheoretic

open import Foundation.Relation.Nullary.Discrete.Base
open import Foundation.Relation.Nullary.Discrete.Instance
open import Foundation.Relation.Nullary.Discrete.List
open import Foundation.Relation.Unary.Countable

∈eℕ-intro : ∀ m n → m ≤ n → m ∈ enum n
∈eℕ-intro zero zero ≤-refl = here refl
∈eℕ-intro (suc m) (suc m) ≤-refl = ∈++-introʳ (here refl)
∈eℕ-intro m (suc n) (≤-step m≤n) = ∈++-introˡ (∈eℕ-intro m n m≤n)

eℕ-length : ∀ n → length (enum n) ≡ suc n
eℕ-length zero = refl
eℕ-length (suc n) =
  length (enum (suc n))               ≡⟨ length-++ (enum n) ⟩
  length (enum n) + length [ suc n ]  ≡⟨ cong (_+ 1) (eℕ-length n) ⟩
  suc n + 1                           ≡⟨ cong suc (+-comm n 1) ⟩
  suc (suc n)                         ∎

∈e2ℕ-intro : ∀ m n → (m , n) ∈ enum (suc (m + n))
∈e2ℕ-intro m n = ∈++-introʳ $ ∈[×]-intro m∈eℕm+n n∈eℕm+n where
  m∈eℕm+n : m ∈ enum (m + n)
  m∈eℕm+n = ∈eℕ-intro m (m + n) m≤m+n
  n∈eℕm+n : n ∈ enum (m + n)
  n∈eℕm+n = ∈eℕ-intro n (m + n) m≤n+m

e2ℕ-length-suc : ∀ n → length (enum (suc n)) ≡ length (enum n) + suc n * suc n
e2ℕ-length-suc n =
  length (enum (suc n))                               ≡⟨ length-++ (enum n) ⟩
  length (enum n) + length (enum n [×] enum n)        ≡⟨ cong (length (enum n) +_) $ [×]-length (enum n) (enum n) ⟩
  length (enum n) + length (enum n) * length (enum n) ≡⟨ cong (length (enum n) +_) $ cong2 _*_ (eℕ-length n) (eℕ-length n) ⟩
  length (enum n) + suc n * suc n                 ∎

e2ℕ-length->n : ∀ n → length (enum n) > n
e2ℕ-length->n zero = ≤-refl
e2ℕ-length->n (suc n) = subst (_> suc n) (e2ℕ-length-suc n) H where
  H : length (enum n) + suc n * suc n > suc n
  H = +-mono-≤ H2 (m≤m*n _ _) where
    H2 : 1 ≤ length (enum n)
    H2 = ≤-trans (s≤s z≤n) (e2ℕ-length->n n)

e2ℕⓂ : ℕ → (ℕ × ℕ) ？
e2ℕⓂ n = enum n [ n ]?

e2ℕⓂ-enum : ∀ p → Σ k ， e2ℕⓂ k ≡ some p
e2ℕⓂ-enum (m , n) with enum (suc (m + n)) [ m , n ]⁻¹? in eq1
... | none rewrite ∈→Σ[]⁻¹? (∈e2ℕ-intro m n) .snd with eq1
... | ()
e2ℕⓂ-enum (m , n) | some k with e2ℕⓂ k in eq2
... | none rewrite (enum k) [ e2ℕ-length->n k ]⁻¹!≡ with eq2
... | ()
e2ℕⓂ-enum (m , n) | some k | some q = k , H where
  --eq1 : e2ℕ (suc (m + n)) [ m , n ]⁻¹? ≡ some k
  --eq2 : e2ℕⓂ k ≡ e2ℕ k [ k ]? ≡ some q
  H : e2ℕⓂ k ≡ some (m , n)
  H with ≤-total k (suc (m + n))
  ... | inj₁ ≤ with cum-≤→Σ cum ≤
  ... | xs , eq3 =
    e2ℕⓂ k                            ≡⟨ eq2 ⟩
    some q                            ≡˘⟨ ++[]? (enum k) eq2 ⟩
    (enum k ++ xs) [ k ]?             ≡˘⟨ cong (_[ k ]?) eq3 ⟩
    enum (suc (m + n)) [ k ]?         ≡⟨ index-inv (enum (suc (m + n))) eq1 ⟩
    some (m , n)                      ∎
  H | inj₂ ≥ with cum-≤→Σ cum ≥
  ... | xs , eq3 =
    e2ℕⓂ k                            ≡⟨ cong (_[ k ]?) eq3 ⟩
    (enum (suc (m + n)) ++ xs) [ k ]? ≡⟨ ++[]? (enum (suc (m + n))) (index-inv (enum (suc (m + n))) eq1) ⟩
    some (m , n)                      ∎

EnumⓂ2ℕ : Ⓜ.Enum (ℕ × ℕ)
EnumⓂ2ℕ = e2ℕⓂ , ∣_∣₁ ∘ e2ℕⓂ-enum

Enumℙ→Ⓜ : {P : A → 𝕋 ℓ} → Enumℙ P → Ⓜ.Enumℙ P
Enumℙ→Ⓜ {A} {P} (mkEnumℙ f f-cum f-wit) = g , g-wit where
  g : ℕ → A ？
  g n with e2ℕⓂ n
  ... | some (m , n) = f m [ n ]?
  ... | none = none
  g-cal : ∀ k {m n} → e2ℕⓂ k ≡ some (m , n) → g k ≡ f m [ n ]?
  g-cal _ eq rewrite eq = refl
  g-wit : ∀ x → P x ↔ g Ⓜ.witness x
  g-wit x = ↔-trans (f-wit x) $ ⇒: 𝟙.map (uncurry H1) ⇐: 𝟙.map (uncurry H2) where
    H1 : ∀ n → x ∈ f n → Ⓜ.Witness g x
    H1 m x∈fn with ∈→Σ[]? x∈fn
    ... | n , fm[n] with e2ℕⓂ-enum (m , n)
    ... | k , eq = k , g-cal k eq ∙ fm[n]
    H2 : ∀ n → g n ≡ some x → Witness f x
    H2 k fm[n] with e2ℕⓂ k
    ... | some (m , n) with []?→∈ (f m) fm[n]
    ... | x∈fm = m , x∈fm

Enumℙ←Ⓜ : {P : A → 𝕋 ℓ} → Ⓜ.Enumℙ P → Enumℙ P
Enumℙ←Ⓜ {A} {P} (f , f-enum) = mkEnumℙ h h-cum h-enum where
  g : 𝕃ₙ A
  g n with f n
  ... | some x = [ x ]
  ... | none = []
  g-cal : ∀ {k x} → f k ≡ some x → g k ≡ [ x ]
  g-cal eq rewrite eq = refl
  wit↔ : ∀ x → Ⓜ.Witness f x ↔ Witness g x
  wit↔ x = ⇒: uncurry H1 ⇐: uncurry H2 where
    H1 : ∀ n → f n ≡ some x → Witness g x
    H1 n fn = n , subst (x ∈_) (g-cal fn) (here refl)
    H2 : ∀ n → x ∈ g n → Ⓜ.Witness f x
    H2 n x∈gn with f n in eq
    H2 n (here refl) | some x = n , eq
  h : 𝕃ₙ A
  h zero = []
  h (suc n) = h n ++ g n
  h-cum : Cumulation h
  h-cum n = g n , refl
  h-enum : ∀ x → P x ↔ h witness x
  h-enum x =
    P x           ↔⟨ f-enum x ⟩
    f Ⓜ.witness x ↔⟨ ↔-map $ wit↔ x ⟩
    g witness x   ↔⟨ ↔-map $ ⇒: uncurry H1 ⇐: uncurry H2 ⟩
    h witness x   ↔∎ where
      H1 : ∀ n → x ∈ g n → Witness h x
      H1 n x∈gn = suc n , ∈++-introʳ x∈gn
      H2 : ∀ n → x ∈ h n → Witness g x
      H2 (suc n) x∈hn++gn with ∈++-elim (h n) x∈hn++gn
      ... | inj₁ x∈hn = H2 n x∈hn
      ... | inj₂ x∈gn = n , x∈gn

Enumℙ↔Ⓜ : Enumℙ P ↔ Ⓜ.Enumℙ P
Enumℙ↔Ⓜ = ⇒: Enumℙ→Ⓜ ⇐: Enumℙ←Ⓜ

Enum↔Ⓜ : Enum A ↔ Ⓜ.Enum A
Enum↔Ⓜ {A} =
  Enum A                  ↔⟨ Enum↔ℙ ⟩
  Enumℙ (λ (_ : A) → ⊤)   ↔⟨ Enumℙ↔Ⓜ ⟩
  Ⓜ.Enumℙ (λ (_ : A) → ⊤) ↔˘⟨ Ⓜ.Enum↔ℙ ⟩
  Ⓜ.Enum A                ↔∎

enumerableℙ↔Ⓜ : enumerableℙ P ↔ Ⓜ.enumerableℙ P
enumerableℙ↔Ⓜ = ↔-map Enumℙ↔Ⓜ

enumerable↔Ⓜ : enumerable A ↔ Ⓜ.enumerable A
enumerable↔Ⓜ {A} = ↔-map Enum↔Ⓜ

discr→enum→count : ⦃ discrete A ⦄ → enumerable A → countable A
discr→enum→count enumA = Ⓜ.discr→enum→count (enumerable↔Ⓜ .⇒ enumA)
