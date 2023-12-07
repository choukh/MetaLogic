module Foundation.Function.Bijection where

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Prop.Universe
open import Foundation.Data.Sigma
open import Foundation.Function.Isomorphism

open import Cubical.Functions.Embedding
  using (isEmbedding; isEmbedding→Inj; injEmbedding)

open import Cubical.Functions.Surjection
  using (isEquiv→isEmbedding×isSurjection; isEmbedding×isSurjection→isEquiv)
  renaming (isSurjection to surjective🧊)

open import Cubical.Foundations.Equiv
  using (isEquiv; isPropIsEquiv)

private variable
  f : A → B

injective : (A → B) → 𝕋 _
injective f = ∀ {x y} → f x ≡ f y → x ≡ y

surjective : (A → B) → 𝕋 _
surjective f = ∀ y → ∃ x ， f x ≡ y

bijective : (A → B) → 𝕋 _
bijective f = injective f × surjective f

isPropInjective : {f : A → B} → isSet A → isProp (injective f)
isPropInjective sA = isPropΠ̅2 λ _ _ → isProp→ (sA _ _)

isPropSurjective : {f : A → B} → isProp (surjective f)
isPropSurjective = isPropΠ λ _ → 𝟙.squash

isPropBijective : {f : A → B} → isSet A → isProp (bijective f)
isPropBijective sA = isProp× (isPropInjective sA) isPropSurjective

_↣_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ↣ B = Σ (A → B) injective

_↠_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ↠ B = Σ (A → B) surjective

_⤖_ : 𝕋 ℓ → 𝕋 ℓ′ → 𝕋 _
A ⤖ B = Σ (A → B) bijective

injective🧊 : (A → B) → 𝕋 _
injective🧊 f = ∀ x y → f x ≡🧊 f y → x ≡🧊 y

injective→🧊 : injective f → injective🧊 f
injective→🧊 inj x y = Eq→🧊 ∘ inj ∘ Eq←🧊

injective←🧊 : injective🧊 f → injective f
injective←🧊 inj = Eq←🧊 ∘ inj _ _ ∘ Eq→🧊 

surjective→🧊 : surjective f → surjective🧊 f
surjective→🧊 surj y = 𝟙.map (λ (x , eq) → x , Eq→🧊 eq) (surj y)

surjective←🧊 : surjective🧊 f → surjective f
surjective←🧊 surj y = 𝟙.map (λ (x , eq) → x , Eq←🧊 eq) (surj y)

isEquiv≡bijective : {f : A → B} → isSet A → isSet B → isEquiv f ≡ bijective f
isEquiv≡bijective sA sB = propExt (isProp←🧊 $ isPropIsEquiv _) (isPropBijective sA) $
  ⇒: (λ equiv → let emb , surj = isEquiv→isEmbedding×isSurjection equiv in
    (injective←🧊 $ isEmbedding→Inj emb) , surjective←🧊 surj)
  ⇐: (λ (inj , surj) → isEmbedding×isSurjection→isEquiv $
    injEmbedding (isSet→🧊 sB) (injective→🧊 inj _ _) , surjective→🧊 surj)

Equiv≡Bij : isSet A → isSet B → (A ≃🧊 B) ≡ (A ⤖ B)
Equiv≡Bij sA sB = Σcong₂ λ x → isEquiv≡bijective sA sB

Iso≡Bij : isSet A → isSet B → (A ≅ B) ≡ (A ⤖ B)
Iso≡Bij sA sB = ua (Iso≅Equiv🧊 sA) ∙ Equiv≡Bij sA sB
