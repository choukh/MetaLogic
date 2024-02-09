module Foundation.Prop.Iff where

open import Foundation.Prelude
open import Foundation.Prop.Truncation

--------------------------------------------------------------------------------
-- Bi-implication (iff) of Type (which has a seperate proof of prop-hood)

infix 3 _↔_
infix 8 ⇒:_⇐:_
record _↔_ (A : 𝕋 ℓ) (B : 𝕋 ℓ′) : 𝕋 (ℓ ⊔ ℓ′) where
  constructor ⇒:_⇐:_
  field
    ⇒ : A → B
    ⇐ : B → A

open _↔_ public

--------------------------------------------------------------------------------
-- Iff is an equivalence relation

↔-refl : A ↔ A
↔-refl = ⇒: id ⇐: id

↔-sym : A ↔ B → B ↔ A
↔-sym A↔B = ⇒: ⇐ A↔B ⇐: ⇒ A↔B

↔-trans : A ↔ B → B ↔ C → A ↔ C
↔-trans A↔B B↔C = ⇒: ⇒ B↔C ∘ ⇒ A↔B ⇐: ⇐ A↔B ∘ ⇐ B↔C

--------------------------------------------------------------------------------
-- Interactions of iff with equality

≡→↔ : A ≡ B → A ↔ B
≡→↔ refl = ↔-refl

≡-↔-trans : A ≡ B → B ↔ C → A ↔ C
≡-↔-trans A≡B B↔C = subst (_↔ _) A≡B B↔C

↔-≡-trans : A ↔ B → B ≡ C → A ↔ C
↔-≡-trans A↔B B≡C = subst (_ ↔_) (sym B≡C) A↔B

--------------------------------------------------------------------------------
-- Syntax for chains of iff reasoning

infixr 2 step-↔ step-↔˘ step-↔≡ step-↔≡˘ _↔⟨⟩_
infix  3 _↔∎

step-↔ : (A : 𝕋 ℓ) → B ↔ C → A ↔ B → A ↔ C
step-↔ _ = flip ↔-trans

syntax step-↔ A B p = A ↔⟨ p ⟩ B

step-↔˘ : (A : 𝕋 ℓ) → B ↔ C → B ↔ A → A ↔ C
step-↔˘ _ = flip (↔-trans ∘ ↔-sym)

syntax step-↔˘ A B p = A ↔˘⟨ p ⟩ B

step-↔≡ : (A : 𝕋 ℓ) → B ↔ C → A ≡ B → A ↔ C
step-↔≡ _ = flip ≡-↔-trans

syntax step-↔≡ A B p = A ↔≡⟨ p ⟩ B

step-↔≡˘ : (A : 𝕋 ℓ) → B ↔ C → B ≡ A → A ↔ C
step-↔≡˘ _ = flip (≡-↔-trans ∘ sym)

syntax step-↔≡˘ A B p = A ↔≡˘⟨ p ⟩ B

_↔⟨⟩_ : (A : 𝕋 ℓ) → A ↔ B → A ↔ B
_ ↔⟨⟩ A↔B = A↔B

_↔∎ : (A : 𝕋 ℓ) → A ↔ A
_ ↔∎ = ↔-refl

--------------------------------------------------------------------------------
-- Some congruence properties of iff

↔-cong : {x y : A} (P : A → 𝕋 ℓ) → x ≡ y → P x ↔ P y
↔-cong _ refl = ↔-refl

↔-cong-≡ : ∀ {a b c d : A} → a ≡ b → c ≡ d → (a ≡ c) ↔ (b ≡ d)
↔-cong-≡ a≡b c≡d = ⇒: (λ a≡c → sym a≡b ∙ a≡c ∙ c≡d)
                   ⇐: (λ b≡d → a≡b     ∙ b≡d ∙ sym c≡d)

↔-cong-→ : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
↔-cong-→ A↔B C↔D = ⇒: (λ f x → ⇒ C↔D (f $ ⇐ A↔B x))
                   ⇐: (λ g x → ⇐ C↔D (g $ ⇒   A↔B x))

↔-cong-Π : (∀ x → P x ↔ Q x) → (∀ x → P x) ↔ (∀ x → Q x)
↔-cong-Π ↔ = ⇒: (λ P x → ⇒ (↔ x) $ P x)
             ⇐: (λ Q x → ⇐ (↔ x) $ Q x)

--------------------------------------------------------------------------------
-- Proof of prop-hood

unquoteDecl iffIsoΣ = declareRecordIsoΣ iffIsoΣ (quote _↔_)

isProp↔ : isProp A → isProp B → isProp (A ↔ B)
isProp↔ propA propB = subst (λ X → isProp X) (ua $ Iso←🧊 $ iffIsoΣ) $
  isPropΣ (isProp→ propB) λ _ → isProp→ propA

--------------------------------------------------------------------------------
-- With propositional truncation

↔-map : A ↔ B → ∥ A ∥₁ ↔ ∥ B ∥₁
↔-map iff = ⇒: 𝟙.map (iff .⇒) ⇐: 𝟙.map (iff .⇐)

∥↔∥-map : ∥ A ↔ B ∥₁ → ∥ A ∥₁ ↔ ∥ B ∥₁
∥↔∥-map = 𝟙.rec (isProp↔ 𝟙.squash 𝟙.squash) ↔-map

--------------------------------------------------------------------------------
-- Stdlib

open import Function as ⓢ
  using (_⇔_; mk⇔)

open ⓢ.Equivalence

Iff→ⓢ : A ↔ B → A ⇔ B
Iff→ⓢ (⇒: ⇒ ⇐: ⇐) = mk⇔ ⇒ ⇐

Iff←ⓢ : A ⇔ B → A ↔ B
Iff←ⓢ H = ⇒: H .to ⇐: H .from

isProp⇔ : isProp A → isProp B → isProp (A ⇔ B)
isProp⇔ {A} {B} pA pB
  record { to = f₁ ; from = g₁ ; to-cong = f-cong₁ ; from-cong = g-cong₁ }
  record { to = f₂ ; from = g₂ ; to-cong = f-cong₂ ; from-cong = g-cong₂ }
  with isProp→ pB f₁ f₂ | isProp→ pA g₁ g₂
... | refl | refl = subst2 (λ x y → _ ≡ record { to-cong = x ; from-cong = y })
  (isProp-f-cong f-cong₁ f-cong₂) (isProp-g-cong g-cong₁ g-cong₂) refl
  where
  isProp-f-cong : isProp (∀ {x y} → x ≡ y → f₁ x ≡ f₁ y)
  isProp-f-cong = isPropΠ̅2 λ _ _ → isProp→ (isProp→isSet pB _ _)
  isProp-g-cong : isProp (∀ {x y} → x ≡ y → g₁ x ≡ g₁ y)
  isProp-g-cong = isPropΠ̅2 λ _ _ → isProp→ (isProp→isSet pA _ _)

Iff→←ⓢ : isProp A → isProp B → (H : A ⇔ B) → Iff→ⓢ (Iff←ⓢ H) ≡ H
Iff→←ⓢ pA pB _ = isProp⇔ pA pB _ _

Iff←→ⓢ : isProp A → isProp B → (H : A ↔ B) → Iff←ⓢ (Iff→ⓢ H) ≡ H
Iff←→ⓢ pA pB _ = isProp↔ pA pB _ _

Iff≅ⓢ : isProp A → isProp B → (A ↔ B) ≅ (A ⇔ B)
Iff≅ⓢ pA pB = mk≅ Iff→ⓢ Iff←ⓢ (Iff→←ⓢ pA pB) (Iff←→ⓢ pA pB)

Iff≡ⓢ : isProp A → isProp B → (A ↔ B) ≡ (A ⇔ B)
Iff≡ⓢ pA pB = ua $ Iff≅ⓢ pA pB
