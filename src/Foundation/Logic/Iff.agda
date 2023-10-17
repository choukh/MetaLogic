module Foundation.Logic.Iff where

open import Foundation.Prelude
open import Foundation.Logic.Basic

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

＝→↔ : A ＝ B → A ↔ B
＝→↔ refl = ↔-refl

＝-↔-trans : A ＝ B → B ↔ C → A ↔ C
＝-↔-trans A＝B B↔C = subst (_↔ _) A＝B B↔C

↔-＝-trans : A ↔ B → B ＝ C → A ↔ C
↔-＝-trans A↔B B＝C = subst (_ ↔_) (sym B＝C) A↔B

--------------------------------------------------------------------------------
-- Syntax for chains of iff reasoning

infixr 2 step-↔ step-↔˘ step-↔＝ step-↔＝˘ _↔⟨⟩_
infix  3 _↔∎

step-↔ : (A : 𝕋 ℓ) → B ↔ C → A ↔ B → A ↔ C
step-↔ _ = flip ↔-trans

syntax step-↔ A B p = A ↔⟨ p ⟩ B

step-↔˘ : (A : 𝕋 ℓ) → B ↔ C → B ↔ A → A ↔ C
step-↔˘ _ = flip (↔-trans ∘ ↔-sym)

syntax step-↔˘ A B p = A ↔˘⟨ p ⟩ B

step-↔＝ : (A : 𝕋 ℓ) → B ↔ C → A ＝ B → A ↔ C
step-↔＝ _ = flip ＝-↔-trans

syntax step-↔＝ A B p = A ↔＝⟨ p ⟩ B

step-↔＝˘ : (A : 𝕋 ℓ) → B ↔ C → B ＝ A → A ↔ C
step-↔＝˘ _ = flip (＝-↔-trans ∘ sym)

syntax step-↔＝˘ A B p = A ↔＝˘⟨ p ⟩ B

_↔⟨⟩_ : (A : 𝕋 ℓ) → A ↔ B → A ↔ B
_ ↔⟨⟩ A↔B = A↔B

_↔∎ : (A : 𝕋 ℓ) → A ↔ A
_ ↔∎ = ↔-refl

--------------------------------------------------------------------------------
-- Proof of prop-hood

unquoteDecl iffIsoΣ = declareRecordIsoΣ iffIsoΣ (quote _↔_)

isProp↔ : isProp A → isProp B → isProp (A ↔ B)
isProp↔ propA propB = subst (λ X → isProp X) (ua $ Iso←🧊 $ iffIsoΣ) $
  isPropΣ (isProp→ propB) λ _ → isProp→ propA

∥∥-↔ : ∥ A ↔ B ∥₁ → ∥ A ∥₁ ↔ ∥ B ∥₁
∥∥-↔ = rec₁ (isProp↔ is₁ is₁) λ iff →
  ⇒: map₁ (iff .⇒) ⇐: map₁ (iff .⇐)
