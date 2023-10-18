module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
open import Foundation.Function.Bundles

open import Foundation.Logic
open import Foundation.Logic.ConstructiveEpsilon

open import Foundation.Data.Nat
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Maybe
open import Foundation.Data.Sigma
open import Foundation.Data.List
open import Foundation.Data.List.Cumulative
open import Foundation.Data.List.SetTheoretic
open import Foundation.Data.List.Discrete (discrete× discreteℕ discreteℕ)

open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete
open import Foundation.Relation.Unary.Countable

module MaybeView where

  _witness_ : (ℕ → A ？) → A → 𝕋 _
  f witness x = ∃ n ⸴ f n ＝ some x

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ⸴ ∀ (x : A) → f witness x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ⸴ ∀ x → P x ↔ f witness x

  Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
  Enum↔ℙ = ⇒: (λ (f , H) → f , λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
           ⇐: (λ (f , H) → f , λ x → H x .⇒ tt)

  enumerable : 𝕋 ℓ → 𝕋 _
  enumerable A = ∥ Enum A ∥₁

  enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
  enumerableℙ P = ∥ Enumℙ P ∥₁

  enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
  enumerable↔ℙ = ∥∥-↔ ∣ Enum↔ℙ ∣₁

  discrete→enumerable→countable : discrete A → enumerable A → countable A
  discrete→enumerable→countable {A} disA = rec₁ is₁ H where
    H : Enum A → countable A
    H (f , H) = ∣ mk↣ g₁ g₁-inj ∣₁ where
      g : ∀ x → Σ n ⸴ f n ＝ some x
      g x = ε sets dis (H x) where
        sets : isSets (λ n → f n ＝ some x)
        sets n = isProp→isSet $ (isSetMaybe $ discrete→isSet disA) _ _
        dis : ∀ n → Dec (f n ＝ some x)
        dis n = (discreteMaybe disA) _ _
      g₁ : A → ℕ
      g₁ = fst ∘ g
      g₂ : ∀ x → f (g₁ x) ＝ some x
      g₂ = snd ∘ g
      g₁-inj : injective g₁
      g₁-inj {x} {y} eq = some-inj $
        some x   ＝˘⟨ g₂ x ⟩
        f (g₁ x) ＝⟨ cong f eq ⟩
        f (g₁ y) ＝⟨ g₂ y ⟩
        some y   ∎

module ListView where
  module Ⓜ = MaybeView

  _witness_ : 𝕃ₙ A → A → 𝕋 _
  f witness x = ∃ n ⸴ x ∈ f n

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ⸴ Cumulative f ∧ ∀ (x : A) → f witness x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ⸴ Cumulative f ∧ ∀ x → P x ↔ f witness x

  Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
  Enum↔ℙ = ⇒: (λ (f , cum , H) → f , cum , λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
           ⇐: (λ (f , cum , H) → f , cum , λ x → H x .⇒ tt)

  enumerable : 𝕋 ℓ → 𝕋 _
  enumerable A = ∥ Enum A ∥₁

  enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
  enumerableℙ P = ∥ Enumℙ P ∥₁

  enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
  enumerable↔ℙ = ∥∥-↔ ∣ Enum↔ℙ ∣₁

  Enum𝔹 : Enum 𝔹
  Enum𝔹 = (λ _ → true ∷ [ false ]) , (λ n → [] , refl) ,
    λ { true →  exists 0 (here refl)
      ; false → exists 0 (there $ here refl) }

  eℕ : 𝕃ₙ ℕ
  eℕ zero = [ 0 ]
  eℕ (suc n) = eℕ n ++ [ suc n ]

  Enumℕ : Enum ℕ
  Enumℕ = eℕ , (λ n → [ suc n ] , refl) , λ n → exists n (H n) where
    H : ∀ n → n ∈ eℕ n
    H zero = here refl
    H (suc n) = ∈-++⁺ʳ _ (here refl)

  ∈eℕ-intro : ∀ m n → m ≤ n → m ∈ eℕ n
  ∈eℕ-intro zero zero ≤-refl = here refl
  ∈eℕ-intro (suc m) (suc m) ≤-refl = ∈-++⁺ʳ _ (here refl)
  ∈eℕ-intro m (suc n) (≤-step m≤n) = ∈-++⁺ˡ (∈eℕ-intro m n m≤n)

  eℕ-length : ∀ n → length (eℕ n) ＝ suc n
  eℕ-length zero = refl
  eℕ-length (suc n) =
    length (eℕ (suc n))               ＝⟨ length-++ (eℕ n) ⟩
    length (eℕ n) + length [ suc n ]  ＝⟨ cong (_+ 1) (eℕ-length n) ⟩
    suc n + 1                         ＝⟨ cong suc (+-comm n 1) ⟩
    suc (suc n)                       ∎

  Enum× : Enum A → Enum B → Enum (A × B)
  Enum× {A} {B} (f , f-cum , f-enum) (g , g-cum , g-enum) = h , h-cum , h-enum where
    h : 𝕃ₙ (A × B)
    h zero = f 0 [×] g 0
    h (suc n) = h n ++ f n [×] g n
    h-cum : Cumulative h
    h-cum n = f n [×] g n , refl
    h-enum : ∀ xy → h witness xy
    h-enum (x , y) = intro2 (f-enum x) (g-enum y) H where
      H : (Σ n ⸴ x ∈ f n) → (Σ n ⸴ y ∈ g n) → ∃ n ⸴ (x , y) ∈ h n
      H (m , x∈fm) (n , x∈gn) = exists (suc (m + n)) (∈-++⁺ʳ _ H2) where
        H2 : (x , y) ∈ f (m + n) [×] g (m + n)
        H2 = ∈[×]-intro (cum-≤→⊆ f-cum _ _ m≤m+n x∈fm) (cum-≤→⊆ g-cum _ _ m≤n+m x∈gn)

  e2ℕ : 𝕃ₙ (ℕ × ℕ)
  e2ℕ = Enum× Enumℕ Enumℕ .fst

  ∈e2ℕ-intro : ∀ m n → (m , n) ∈ e2ℕ (suc (m + n))
  ∈e2ℕ-intro m n = ∈-++⁺ʳ _ $ ∈[×]-intro m∈eℕm+n n∈eℕm+n where
    m∈eℕm+n : m ∈ eℕ (m + n)
    m∈eℕm+n = ∈eℕ-intro m (m + n) m≤m+n
    n∈eℕm+n : n ∈ eℕ (m + n)
    n∈eℕm+n = ∈eℕ-intro n (m + n) m≤n+m

  e2ℕ-length-zero : length (e2ℕ zero) ＝ suc zero
  e2ℕ-length-zero = refl

  e2ℕ-length-suc : ∀ n → length (e2ℕ (suc n)) ＝ length (e2ℕ n) + suc n * suc n
  e2ℕ-length-suc n =
    length (e2ℕ (suc n))                           ＝⟨ length-++ (e2ℕ n) ⟩
    length (e2ℕ n) + length (eℕ n [×] eℕ n)        ＝⟨ cong (length (e2ℕ n) +_) $ [×]-length (eℕ n) (eℕ n) ⟩
    length (e2ℕ n) + length (eℕ n) * length (eℕ n) ＝⟨ cong (length (e2ℕ n) +_) $ cong2 _*_ (eℕ-length n) (eℕ-length n) ⟩
    length (e2ℕ n) + suc n * suc n                 ∎

  e2ℕ-length->n : ∀ n → length (e2ℕ n) > n
  e2ℕ-length->n zero = ≤-refl
  e2ℕ-length->n (suc n) = subst (_> suc n) (e2ℕ-length-suc n) H where
    H : length (e2ℕ n) + suc n * suc n > suc n
    H = +-mono-≤ H2 (m≤m*n _ _) where
      H2 : 1 ≤ length (e2ℕ n)
      H2 = ≤-trans (s≤s z≤n) (e2ℕ-length->n n)

  e2ℕⓂ : ℕ → (ℕ × ℕ) ？
  e2ℕⓂ n = e2ℕ n [ n ]?

  e2ℕⓂ-witnessing : ∀ p → e2ℕⓂ Ⓜ.witness p
  e2ℕⓂ-witnessing (m , n) with e2ℕ (suc (m + n)) [ m , n ]⁻¹? in eq
  ... | none rewrite x∈→Σ[x]⁻¹ (∈e2ℕ-intro m n) .snd with eq
  ... | ()
  e2ℕⓂ-witnessing (m , n) | some k with e2ℕⓂ k in eq
  ... | none rewrite Σ[<length] (e2ℕ k) (e2ℕ-length->n k) .snd with eq
  ... | ()
  e2ℕⓂ-witnessing (m , n) | some k | some p = exists k $ index-inv (e2ℕ k)
    {!   !}

  EnumⓂ2ℕ : Ⓜ.Enum (ℕ × ℕ)
  EnumⓂ2ℕ = e2ℕⓂ , e2ℕⓂ-witnessing

  Enumℙ→Ⓜ : {P : A → 𝕋 ℓ} → Enumℙ P → Ⓜ.Enumℙ P
  Enumℙ→Ⓜ {A} (f , cum , H) = {!   !} , {!   !}

  Enumℙ←Ⓜ : Ⓜ.Enumℙ P → Enumℙ P
  Enumℙ←Ⓜ = {!   !}

  Enumℙ↔Ⓜ : Enumℙ P ↔ Ⓜ.Enumℙ P
  Enumℙ↔Ⓜ = ⇒: Enumℙ→Ⓜ ⇐: Enumℙ←Ⓜ

  enumerableℙ↔Ⓜ : enumerableℙ P ↔ Ⓜ.enumerableℙ P
  enumerableℙ↔Ⓜ = ∥∥-↔ ∣ Enumℙ↔Ⓜ ∣₁

  enumerable↔Ⓜ : enumerable A ↔ Ⓜ.enumerable A
  enumerable↔Ⓜ {A} =
    enumerable A                  ↔⟨ enumerable↔ℙ ⟩
    enumerableℙ (λ (_ : A) → ⊤)   ↔⟨ enumerableℙ↔Ⓜ ⟩
    Ⓜ.enumerableℙ (λ (_ : A) → ⊤) ↔˘⟨ Ⓜ.enumerable↔ℙ ⟩
    Ⓜ.enumerable A                ↔∎

  discrete→enumerable→countable : discrete A → enumerable A → countable A
  discrete→enumerable→countable disA enumA =
    Ⓜ.discrete→enumerable→countable disA (enumerable↔Ⓜ .⇒ enumA)
  