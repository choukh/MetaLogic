module Foundation.Relation.Unary.Enumerable where

open import Foundation.Prelude
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
open import Foundation.Functions.Injection

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
    H (f , H) = exists g₁ λ x → g₁-inj x where
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
  module 𝕄 = MaybeView

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

  Enumℕ : Enum ℕ
  Enumℕ = f , (λ n → exists [ suc n ] refl) , λ n → exists n (H n) where
    f : 𝕃ₙ ℕ
    f zero = [ 0 ]
    f (suc n) = f n ++ [ suc n ]
    H : ∀ n → n ∈ f n
    H zero = here refl
    H (suc n) = ∈-++⁺ʳ (f n) (here refl)

  Enum× : Enum A → Enum B → Enum (A × B)
  Enum× {A} {B} (f , f-cum , f-enum) (g , _ , g-enum) = h , h-cum , h-enum where
    h : 𝕃ₙ (A × B)
    h zero = f 0 [×] g 0
    h (suc n) = h n ++ f n [×] g n
    h-cum : cumulative h
    h-cum n = exists (f n [×] g n) refl
    h-enum : ∀ xy → h enumerates xy
    h-enum (x , y) = intro₁2 (f-enum x) (g-enum y) aux where
      aux : (Σ n ⸴ x ∈ f n) → (Σ n ⸴ y ∈ g n) → Σ n ⸴ (x , y) ∈ h n
      aux (m , x∈fm) (n , x∈gn) = suc (m + n) , ∈-++⁺ʳ (h (m + n)) aux2 where
        x∈fm+n : ∥ x ∈ f (m + n) ∥₁
        x∈fm+n = intro₁ (cum-≤→⊆ f-cum _ _ m≤m+n) λ sub → sub x∈fm
        aux2 : (x , y) ∈ f (m + n) [×] g (m + n)
        aux2 with f (m + n) in eq
        ... | [] = exfalso₁ (intro₁ x∈fm+n $ subst (x ∈_) (sym eq)) λ ()
        ... | _ ∷ xs = ∈-++⁺ˡ aux3 where
          aux3 : (x , y) ∈ map (_ ,_) (g (m + n))
          aux3 = {!   !}

  Enumℙ→𝕄 : {P : A → 𝕋 ℓ} → Enumℙ P → 𝕄.Enumℙ P
  Enumℙ→𝕄 {A} (f , cum , H) = {!   !} , {!   !}

  Enumℙ←𝕄 : 𝕄.Enumℙ P → Enumℙ P
  Enumℙ←𝕄 = {!   !}

  Enumℙ↔𝕄 : Enumℙ P ↔ 𝕄.Enumℙ P
  Enumℙ↔𝕄 = ⇒: Enumℙ→𝕄 ⇐: Enumℙ←𝕄

  enumerableℙ↔𝕄 : enumerableℙ P ↔ 𝕄.enumerableℙ P
  enumerableℙ↔𝕄 = ∥∥-↔ ∣ Enumℙ↔𝕄 ∣₁

  enumerable↔𝕄 : enumerable A ↔ 𝕄.enumerable A
  enumerable↔𝕄 {A} =
    enumerable A                  ↔⟨ enumerable↔ℙ ⟩
    enumerableℙ (λ (_ : A) → ⊤)   ↔⟨ enumerableℙ↔𝕄 ⟩
    𝕄.enumerableℙ (λ (_ : A) → ⊤) ↔˘⟨ 𝕄.enumerable↔ℙ ⟩
    𝕄.enumerable A                ↔∎

  discrete→enumerable→countable : discrete A → enumerable A → countable A
  discrete→enumerable→countable disA enumA =
    𝕄.discrete→enumerable→countable disA (enumerable↔𝕄 .⇒ enumA)
 