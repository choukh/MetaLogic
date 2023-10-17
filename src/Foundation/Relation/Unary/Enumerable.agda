module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
open import Foundation.Function.Bundles

open import Foundation.Logic.Basic
open import Foundation.Logic.Iff
open import Foundation.Logic.ConstructiveEpsilon

open import Foundation.Data.Nat
open import Foundation.Data.Nat.AlternativeOrder
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.List.Cumulative
open import Foundation.Data.List.SetTheoretic
open import Foundation.Data.Sigma

open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete
open import Foundation.Relation.Unary.Countable

module MaybeView where

  _enumerates_ : (ℕ → A ？) → A → 𝕋 _
  f enumerates x = ∃ n ⸴ f n ＝ some x

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ⸴ ∀ (x : A) → f enumerates x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ⸴ ∀ x → P x ↔ f enumerates x

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

  _enumerates_ : 𝕃ₙ A → A → 𝕋 _
  f enumerates x = ∃ n ⸴ x ∈ f n

  Enum : 𝕋 ℓ → 𝕋 _
  Enum A = Σ f ⸴ cumulative f ∧ ∀ (x : A) → f enumerates x

  Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
  Enumℙ P = Σ f ⸴ cumulative f ∧ ∀ x → P x ↔ f enumerates x

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
  Enum𝔹 = (λ _ → true ∷ [ false ]) , (λ n → exists [] refl) ,
    λ { true →  exists 0 (here refl)
      ; false → exists 0 (there $ here refl) }

  Eℕ : 𝕃ₙ ℕ
  Eℕ zero = [ 0 ]
  Eℕ (suc n) = Eℕ n ++ [ suc n ]

  Enumℕ : Enum ℕ
  Enumℕ = Eℕ , (λ n → exists [ suc n ] refl) , λ n → exists n (H n) where
    H : ∀ n → n ∈ Eℕ n
    H zero = here refl
    H (suc n) = ∈-++⁺ʳ _ (here refl)

  ∈Eℕ-intro : ∀ m n → m ≤ n → m ∈ Eℕ n
  ∈Eℕ-intro zero zero ≤-refl = here refl
  ∈Eℕ-intro (suc m) (suc m) ≤-refl = ∈-++⁺ʳ _ (here refl)
  ∈Eℕ-intro m (suc n) (≤-step m≤n) = ∈-++⁺ˡ (∈Eℕ-intro m n m≤n)

  Eℕ-length : ∀ n → length (Eℕ n) ＝ suc n
  Eℕ-length zero = refl
  Eℕ-length (suc n) =
    length (Eℕ (suc n))               ＝⟨ length-++ (Eℕ n) ⟩
    length (Eℕ n) + length [ suc n ]  ＝⟨ cong (_+ 1) (Eℕ-length n) ⟩
    suc n + 1                         ＝⟨ cong suc (+-comm n 1) ⟩
    suc (suc n)                       ∎

  Enum× : Enum A → Enum B → Enum (A × B)
  Enum× {A} {B} (f , f-cum , f-enum) (g , g-cum , g-enum) = h , h-cum , h-enum where
    h : 𝕃ₙ (A × B)
    h zero = f 0 [×] g 0
    h (suc n) = h n ++ f n [×] g n
    h-cum : cumulative h
    h-cum n = exists (f n [×] g n) refl
    h-enum : ∀ xy → h enumerates xy
    h-enum (x , y) = intro2 (f-enum x) (g-enum y) H where
      H : (Σ n ⸴ x ∈ f n) → (Σ n ⸴ y ∈ g n) → ∃ n ⸴ (x , y) ∈ h n
      H (m , x∈fm) (n , x∈gn) = intro∣ H2 (λ H → suc (m + n) , ∈-++⁺ʳ _ H) where
        x∈fm+n : ∥ x ∈ f (m + n) ∥₁
        x∈fm+n = map₁ (λ sub → sub x∈fm) (cum-≤→⊆ f-cum _ _ m≤m+n)
        x∈gm+n : ∥ y ∈ g (m + n) ∥₁
        x∈gm+n = map₁ (λ sub → sub x∈gn) (cum-≤→⊆ g-cum _ _ m≤n+m)
        H2 : ∥ (x , y) ∈ f (m + n) [×] g (m + n) ∥₁
        H2 = map₁2 ∈[×]-intro x∈fm+n x∈gm+n

  E2ℕ : 𝕃ₙ (ℕ × ℕ)
  E2ℕ = Enum× Enumℕ Enumℕ .fst

  ∈E2ℕ-intro : ∀ m n → (m , n) ∈ E2ℕ (suc (m + n))
  ∈E2ℕ-intro m n = ∈-++⁺ʳ _ $ ∈[×]-intro m∈Eℕm+n n∈Eℕm+n where
    m∈Eℕm+n : m ∈ Eℕ (m + n)
    m∈Eℕm+n = ∈Eℕ-intro m (m + n) m≤m+n
    n∈Eℕm+n : n ∈ Eℕ (m + n)
    n∈Eℕm+n = ∈Eℕ-intro n (m + n) m≤n+m

  E2ℕ-length-zero : length (E2ℕ zero) ＝ suc zero
  E2ℕ-length-zero = refl

  E2ℕ-length-suc : ∀ n → length (E2ℕ (suc n)) ＝ length (E2ℕ n) + suc n * suc n
  E2ℕ-length-suc n =
    length (E2ℕ (suc n))                           ＝⟨ length-++ (E2ℕ n) ⟩
    length (E2ℕ n) + length (Eℕ n [×] Eℕ n)        ＝⟨ cong (length (E2ℕ n) +_) $ [×]-length (Eℕ n) (Eℕ n) ⟩
    length (E2ℕ n) + length (Eℕ n) * length (Eℕ n) ＝⟨ cong (length (E2ℕ n) +_) $ cong2 _*_ (Eℕ-length n) (Eℕ-length n) ⟩
    length (E2ℕ n) + suc n * suc n                 ∎

  E2ℕ-length->n : ∀ n → length (E2ℕ n) > n
  E2ℕ-length->n zero = ≤-refl
  E2ℕ-length->n (suc n) = subst (_> suc n) (E2ℕ-length-suc n) H where
    H : length (E2ℕ n) + suc n * suc n > suc n
    H = +-mono-≤ H2 (m≤m*n _ _) where
      H2 : 1 ≤ length (E2ℕ n)
      H2 = ≤-trans (s≤s z≤n) (E2ℕ-length->n n)

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
 