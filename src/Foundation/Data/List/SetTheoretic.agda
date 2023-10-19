module Foundation.Data.List.SetTheoretic where

open import Foundation.Prelude
open import Foundation.Logic.Basic
open import Foundation.Function.Bundles
open import Foundation.Data.Maybe
open import Foundation.Data.List

open import Data.List.Membership.Propositional public
  using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties public
  using (map-∈↔; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Binary.Subset.Propositional public
  using (_⊆_)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there)

∈→Σ[]? : ∀ {xs : 𝕃 A} {x} → x ∈ xs → Σ n ⸴ xs [ n ]? ＝ some x
∈→Σ[]? {xs = x ∷ xs} (here refl) = 0 , refl
∈→Σ[]? {xs = y ∷ xs} (there x∈xs) with ∈→Σ[]? x∈xs
... | n , H = suc n , H

[]?→∈ : ∀ (xs : 𝕃 A) {x n} → xs [ n ]? ＝ some x → x ∈ xs
[]?→∈ (x ∷ xs) {n = zero} refl = here refl
[]?→∈ (y ∷ xs) {n = suc n} eq = there $ []?→∈ xs eq

∈map-intro : ∀ {f : A → B} {xs y} → (Σ x ⸴ x ∈ xs ∧ y ＝ f x) → y ∈ map f xs
∈map-intro {f} = Iso←ⓢ (map-∈↔ f) .fun

infixr 6 _[×]_
_[×]_ : 𝕃 A → 𝕃 B → 𝕃 (A × B)
[] [×] ys = []
(x ∷ xs) [×] ys = map (x ,_) ys ++ xs [×] ys

∈[×]-intro : ∀ {xs : 𝕃 A} {ys : 𝕃 B} {x y} → x ∈ xs → y ∈ ys → (x , y) ∈ xs [×] ys
∈[×]-intro {xs = _ ∷ xs} (here refl) y∈ = ∈-++⁺ˡ $ ∈map-intro $ _ , y∈ , refl
∈[×]-intro {xs = _ ∷ xs} (there x∈)  y∈ = ∈-++⁺ʳ _ $ ∈[×]-intro x∈ y∈

[×]-length : (xs : 𝕃 A) (ys : 𝕃 B) → length (xs [×] ys) ＝ length xs * length ys
[×]-length [] _ = refl
[×]-length (x ∷ xs) ys =
  length (map (x ,_) ys ++ xs [×] ys)         ＝⟨ length-++ (map (x ,_) ys) ⟩
  length (map (x ,_) ys) + length (xs [×] ys) ＝⟨ cong (_+ _) (length-map _ ys) ⟩
  length ys + length (xs [×] ys)              ＝⟨ cong (_ +_) ([×]-length xs ys) ⟩
  length ys + length xs * length ys           ∎
