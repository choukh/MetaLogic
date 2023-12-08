module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
open import Foundation.Function.Bijection
open import Foundation.Prop.Truncation

open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Data.Nat.ConstructiveEpsilon

open import Foundation.Data.Nat
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Maybe
open import Foundation.Data.Sigma
open import Foundation.Data.Sum
open import Foundation.Data.List
open import Foundation.Data.List.Cumulation
open import Foundation.Data.List.SetTheoretic
open import Foundation.Data.List.Discrete (discrete× discreteℕ discreteℕ)

open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete
open import Foundation.Relation.Unary.Countable

module MaybeView where

  Witness : (ℕ → A ？) → A → 𝕋 _
  Witness f x = Σ n ， f n ≡ some x

  _witness_ : (ℕ → A ？) → A → 𝕋 _
  f witness x = ∥ Witness f x ∥₁

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ， ∀ (x : A) → f witness x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ， ∀ x → P x ↔ f witness x

  Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
  Enum↔ℙ = ⇒: (λ (f , H) → f , λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
           ⇐: (λ (f , H) → f , λ x → H x .⇒ tt)

  enumerable : 𝕋 ℓ → 𝕋 _
  enumerable A = ∥ Enum A ∥₁

  enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
  enumerableℙ P = ∥ Enumℙ P ∥₁

  enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
  enumerable↔ℙ = ↔-map Enum↔ℙ

  discr→enum→count : discrete A → enumerable A → countable A
  discr→enum→count {A} disA = 𝟙.map H where
    H : Enum A → A ↣ ℕ
    H (f , H) = g₁ , g₁-inj where
      g : ∀ x → Witness f x
      g x = ε sets dis (H x) where
        sets : isSets (λ n → f n ≡ some x)
        sets n = isProp→isSet $ (isSetMaybe $ discrete→isSet disA) _ _
        dis : ∀ n → Dec (f n ≡ some x)
        dis n = (discreteMaybe disA) _ _
      g₁ : A → ℕ
      g₁ = fst ∘ g
      g₂ : ∀ x → f (g₁ x) ≡ some x
      g₂ = snd ∘ g
      g₁-inj : injective g₁
      g₁-inj {x} {y} eq = some-inj $
        some x   ≡˘⟨ g₂ x ⟩
        f (g₁ x) ≡⟨ cong f eq ⟩
        f (g₁ y) ≡⟨ g₂ y ⟩
        some y   ∎

module ListView where
  module Ⓜ = MaybeView

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

  Enum𝔹 : Enum 𝔹
  Enum𝔹 = mkEnum (λ _ → true ∷ [ false ]) (λ n → [] , refl)
    λ { true →  ex 0 (here refl)
      ; false → ex 0 (there $ here refl) }

  eℕ : 𝕃ₙ ℕ
  eℕ zero = [ 0 ]
  eℕ (suc n) = eℕ n ++ [ suc n ]

  Enumℕ : Enum ℕ
  Enumℕ = mkEnum eℕ (λ n → [ suc n ] , refl) λ n → ex n (H n) where
    H : ∀ n → n ∈ eℕ n
    H zero = here refl
    H (suc n) = ∈-++⁺ʳ _ (here refl)

  ∈eℕ-intro : ∀ m n → m ≤ n → m ∈ eℕ n
  ∈eℕ-intro zero zero ≤-refl = here refl
  ∈eℕ-intro (suc m) (suc m) ≤-refl = ∈-++⁺ʳ _ (here refl)
  ∈eℕ-intro m (suc n) (≤-step m≤n) = ∈-++⁺ˡ (∈eℕ-intro m n m≤n)

  eℕ-length : ∀ n → length (eℕ n) ≡ suc n
  eℕ-length zero = refl
  eℕ-length (suc n) =
    length (eℕ (suc n))               ≡⟨ length-++ (eℕ n) ⟩
    length (eℕ n) + length [ suc n ]  ≡⟨ cong (_+ 1) (eℕ-length n) ⟩
    suc n + 1                         ≡⟨ cong suc (+-comm n 1) ⟩
    suc (suc n)                       ∎

  Enum× : Enum A → Enum B → Enum (A × B)
  Enum× {A} {B} (mkEnum f f-cum f-wit) (mkEnum g g-cum g-wit) = mkEnum h h-cum h-wit where
    h : 𝕃ₙ (A × B)
    h zero = f 0 [×] g 0
    h (suc n) = h n ++ f n [×] g n
    h-cum : Cumulation h
    h-cum n = f n [×] g n , refl
    h-wit : ∀ xy → h witness xy
    h-wit (x , y) = 𝟙.map2 H (f-wit x) (g-wit y) where
      H : Witness f x → Witness g y → Witness h (x , y)
      H (m , x∈fm) (n , x∈gn) = suc (m + n) , ∈-++⁺ʳ _ H2 where
        H2 : (x , y) ∈ f (m + n) [×] g (m + n)
        H2 = ∈[×]-intro (cum-≤→⊆ f-cum m≤m+n x∈fm) (cum-≤→⊆ g-cum m≤n+m x∈gn)

  instance
    Enum2ℕ : Enum (ℕ × ℕ)
    Enum2ℕ = Enum× Enumℕ Enumℕ

  ∈e2ℕ-intro : ∀ m n → (m , n) ∈ enum (suc (m + n))
  ∈e2ℕ-intro m n = ∈-++⁺ʳ _ $ ∈[×]-intro m∈eℕm+n n∈eℕm+n where
    m∈eℕm+n : m ∈ eℕ (m + n)
    m∈eℕm+n = ∈eℕ-intro m (m + n) m≤m+n
    n∈eℕm+n : n ∈ eℕ (m + n)
    n∈eℕm+n = ∈eℕ-intro n (m + n) m≤n+m

  e2ℕ-length-zero : length (enum zero) ≡ suc zero
  e2ℕ-length-zero = refl

  e2ℕ-length-suc : ∀ n → length (enum (suc n)) ≡ length (enum n) + suc n * suc n
  e2ℕ-length-suc n =
    length (enum (suc n))                           ≡⟨ length-++ (enum n) ⟩
    length (enum n) + length (eℕ n [×] eℕ n)        ≡⟨ cong (length (enum n) +_) $ [×]-length (eℕ n) (eℕ n) ⟩
    length (enum n) + length (eℕ n) * length (eℕ n) ≡⟨ cong (length (enum n) +_) $ cong2 _*_ (eℕ-length n) (eℕ-length n) ⟩
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
  ... | none rewrite x∈→Σ[x]⁻¹? (∈e2ℕ-intro m n) .snd with eq1
  ... | ()
  e2ℕⓂ-enum (m , n) | some k with e2ℕⓂ k in eq2
  ... | none rewrite Σ[<length]? (Enum2ℕ .enum k) (e2ℕ-length->n k) .snd with eq2
  ... | ()
  e2ℕⓂ-enum (m , n) | some k | some q = k , H where
    --eq1 : e2ℕ (suc (m + n)) [ m , n ]⁻¹? ≡ some k
    --eq2 : e2ℕⓂ k ≡ e2ℕ k [ k ]? ≡ some q
    H : e2ℕⓂ k ≡ some (m , n)
    H with ≤-total k (suc (m + n))
    ... | inj₁ ≤ with cum-≤→++ cum ≤
    ... | xs , eq3 =
      e2ℕⓂ k                            ≡⟨ eq2 ⟩
      some q                            ≡˘⟨ ++[]? (enum k) eq2 ⟩
      (enum k ++ xs) [ k ]?             ≡˘⟨ cong (_[ k ]?) eq3 ⟩
      enum (suc (m + n)) [ k ]?         ≡⟨ index-inv (enum (suc (m + n))) eq1 ⟩
      some (m , n)                      ∎
    H | inj₂ ≥ with cum-≤→++ cum ≥
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
        H1 n x∈gn = suc n , ∈-++⁺ʳ _ x∈gn
        H2 : ∀ n → x ∈ h n → Witness g x
        H2 (suc n) x∈hn++gn with ∈-++⁻ (h n) x∈hn++gn
        ... | inj₁ x∈hn = H2 n x∈hn
        ... | inj₂ x∈gn = n , x∈gn

  Enumℙ↔Ⓜ : Enumℙ P ↔ Ⓜ.Enumℙ P
  Enumℙ↔Ⓜ = ⇒: Enumℙ→Ⓜ ⇐: Enumℙ←Ⓜ

  enumerableℙ↔Ⓜ : enumerableℙ P ↔ Ⓜ.enumerableℙ P
  enumerableℙ↔Ⓜ = ↔-map Enumℙ↔Ⓜ

  enumerable↔Ⓜ : enumerable A ↔ Ⓜ.enumerable A
  enumerable↔Ⓜ {A} =
    enumerable A                  ↔⟨ enumerable↔ℙ ⟩
    enumerableℙ (λ (_ : A) → ⊤)   ↔⟨ enumerableℙ↔Ⓜ ⟩
    Ⓜ.enumerableℙ (λ (_ : A) → ⊤) ↔˘⟨ Ⓜ.enumerable↔ℙ ⟩
    Ⓜ.enumerable A                ↔∎

  discr→enum→count : discrete A → enumerable A → countable A
  discr→enum→count disA enumA =
    Ⓜ.discr→enum→count disA (enumerable↔Ⓜ .⇒ enumA)
