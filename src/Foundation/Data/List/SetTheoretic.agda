module Foundation.Data.List.SetTheoretic where

open import Foundation.Prelude

open import Foundation.Function.Isomorphism
open import Foundation.Data.Maybe
open import Foundation.Data.List
open import Foundation.Data.Sigma
open import Foundation.Data.Sum

open import Data.List.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties public
  using (map-∈↔; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-concat⁺′)
open import Data.List.Relation.Binary.Subset.Propositional public
  using (_⊆_)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there)

∈→Σ[]? : ∀ {xs : 𝕃 A} {x} → x ∈ xs → Σ n ， xs [ n ]? ≡ some x
∈→Σ[]? {xs = x ∷ xs} (here refl) = 0 , refl
∈→Σ[]? {xs = y ∷ xs} (there x∈xs) with ∈→Σ[]? x∈xs
... | n , H = suc n , H

[]?→∈ : ∀ (xs : 𝕃 A) {x n} → xs [ n ]? ≡ some x → x ∈ xs
[]?→∈ (x ∷ xs) {n = zero} refl = here refl
[]?→∈ (y ∷ xs) {n = suc n} eq = there $ []?→∈ xs eq

∈map-intro : ∀ {f : A → B} {x xs y} → x ∈ xs → y ≡ f x → y ∈ map f xs
∈map-intro {f} H1 H2 = Iso←ⓢ (map-∈↔ f) .fun $ _ , H1 , H2

∈map-elim : ∀ {f : A → B} {xs y} → y ∈ map f xs → Σ x ， x ∈ xs × y ≡ f x
∈map-elim {f} = Iso←ⓢ (map-∈↔ f) .inv

map⊆P-intro : {xs : 𝕃 A} {f : A → B} →
  (∀ x → x ∈ xs → P (f x)) → ∀ y → y ∈ map f xs → P y
map⊆P-intro {P} H y y∈map with ∈map-elim y∈map
... | x , x∈xs , y≡fx = subst P y≡fx $ H x x∈xs

infixr 6 _[×]_
_[×]_ : 𝕃 A → 𝕃 B → 𝕃 (A × B)
[] [×] ys = []
(x ∷ xs) [×] ys = map (x ,_) ys ++ xs [×] ys

∈[×]-intro : ∀ {xs : 𝕃 A} {ys : 𝕃 B} {x y} → x ∈ xs → y ∈ ys → (x , y) ∈ xs [×] ys
∈[×]-intro {xs = _ ∷ xs} (here refl) y∈ = ∈-++⁺ˡ $ ∈map-intro y∈ refl
∈[×]-intro {xs = _ ∷ xs} (there x∈)  y∈ = ∈-++⁺ʳ _ $ ∈[×]-intro x∈ y∈

∈[×]-elim : ∀ {xs : 𝕃 A} {ys : 𝕃 B} {p@(x , y) : A × B} → p ∈ xs [×] ys → x ∈ xs × y ∈ ys
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
  