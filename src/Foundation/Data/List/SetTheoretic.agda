module Foundation.Data.List.SetTheoretic where

open import Foundation.Prelude

open import Foundation.Function.Isomorphism
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.Sigma
open import Foundation.Data.Sum

open import Data.List.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties as Ⓜ public
  using (map-∈↔; ∈-++⁺ˡ; ∈-++⁻; ∈-concat⁺′; ∈-concat⁻′)
open import Data.List.Relation.Binary.Subset.Propositional public
  using (_⊆_)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there)

private variable
  n : ℕ
  x : A
  y : B
  z : C
  xs : 𝕃 A
  ys : 𝕃 B
  f : A → B

------------------------------------------------------------------------
-- Membership

∈-++⁺ʳ : x ∈ ys → x ∈ xs ++ ys
∈-++⁺ʳ = Ⓜ.∈-++⁺ʳ _

∈→Σ[]? : x ∈ xs → Σ n ， xs [ n ]? ≡ some x
∈→Σ[]? {xs = x ∷ xs} (here refl) = 0 , refl
∈→Σ[]? {xs = y ∷ xs} (there x∈xs) with ∈→Σ[]? x∈xs
... | n , H = suc n , H

[]?→∈ : ∀ (xs : 𝕃 A) → xs [ n ]? ≡ some x → x ∈ xs
[]?→∈ {n = zero} (x ∷ xs) refl = here refl
[]?→∈ {n = suc n} (y ∷ xs) eq = there $ []?→∈ xs eq

∈map-intro : x ∈ xs → y ≡ f x → y ∈ map f xs
∈map-intro {f} H1 H2 = Iso←ⓢ (map-∈↔ f) .fun $ _ , H1 , H2

∈map-elim : y ∈ map f xs → Σ x ， x ∈ xs × y ≡ f x
∈map-elim {f} = Iso←ⓢ (map-∈↔ f) .inv

map⊆P-intro : (∀ x → x ∈ xs → P (f x)) → ∀ y → y ∈ map f xs → P y
map⊆P-intro {P} H y y∈map with ∈map-elim y∈map
... | x , x∈xs , y≡fx = subst P y≡fx $ H x x∈xs

infixr 6 _[×]_
_[×]_ : 𝕃 A → 𝕃 B → 𝕃 (A × B)
[] [×] ys = []
(x ∷ xs) [×] ys = map (x ,_) ys ++ xs [×] ys

∈[×]-intro : x ∈ xs → y ∈ ys → (x , y) ∈ xs [×] ys
∈[×]-intro {xs = _ ∷ xs} (here refl) y∈ = ∈-++⁺ˡ $ ∈map-intro y∈ refl
∈[×]-intro {xs = _ ∷ xs} (there x∈)  y∈ = ∈-++⁺ʳ $ ∈[×]-intro x∈ y∈

∈[×]-elim : {p@(x , y) : A × B} → p ∈ xs [×] ys → x ∈ xs × y ∈ ys
∈[×]-elim {xs = x ∷ xs} {ys} p∈ with ∈-++⁻ (map (x ,_) ys) p∈
∈[×]-elim _ | inj₁ H with ∈map-elim H
... | y , y∈ , refl = here refl , y∈
∈[×]-elim _ | inj₂ H with ∈[×]-elim H
... | H1 , H2 = there H1 , H2

[×]-length : (xs : 𝕃 A) (ys : 𝕃 B) → length (xs [×] ys) ≡ length xs * length ys
[×]-length [] _ = refl
[×]-length (x ∷ xs) ys =
  length (map (x ,_) ys ++ xs [×] ys)         ≡⟨ length-++ (map (x ,_) ys) ⟩
  length (map (x ,_) ys) + length (xs [×] ys) ≡⟨ cong (_+ _) (length-map _ ys) ⟩
  length ys + length (xs [×] ys)              ≡⟨ cong (_ +_) ([×]-length xs ys) ⟩
  length ys + length xs * length ys           ∎

∈map[×]-intro : {f : A × B → C} → x ∈ xs → y ∈ ys → f (x , y) ∈ map f (xs [×] ys)
∈map[×]-intro H1 H2 = ∈map-intro (∈[×]-intro H1 H2) refl

∈map[×]-elim : {f : A × B → C} → z ∈ map f (xs [×] ys) → Σ x ， Σ y ， x ∈ xs × y ∈ ys × z ≡ f (x , y)
∈map[×]-elim z∈ with ∈map-elim z∈
... | (x , y) , xy∈ , refl with ∈[×]-elim xy∈
... | x∈ , y∈ = x , y , x∈ , y∈ , refl

------------------------------------------------------------------------
-- Subset

∷⊆∷ : xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
∷⊆∷ sub (here refl) = here refl
∷⊆∷ sub (there x∈xs) = there (sub x∈xs)

map⊆map : xs ⊆ ys → map f xs ⊆ map f ys
map⊆map sub H with ∈map-elim H
... | (x , x∈xs , refl) = ∈map-intro (sub x∈xs) refl
