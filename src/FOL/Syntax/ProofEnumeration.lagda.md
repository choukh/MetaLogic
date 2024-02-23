---
url: fol.syntax.proof-enumeration
---

# 一阶逻辑 ▸ 语法 ▸⁻ 证明的枚举

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import Foundation.Relation.Nullary.Discrete.List
open import FOL.Language.Base

module FOL.Syntax.ProofEnumeration (ℒ : Language) where
open import FOL.Syntax.Base ℒ
open import FOL.Syntax.Discrete ℒ
open import FOL.Syntax.Enumeration ℒ
instance _ = ℒ
```

```agda
enumProof : Enumℙ (Γ ⊢_)
enumProof {Γ} = mkEnumℙ (e Γ) {!   !} {!   !} where
```

```agda
  e : Context → 𝕃ₙ Formula
  e Γ zero = Γ
  e Γ (suc n) = e Γ n
    {- ImpI -}   ++ concat (map (λ φ → map (φ →̇_) (e (φ ∷ Γ) n)) (enum n))
    {- ImpE -}   ++ map snd (filter (λ { (φ , ψ) → φ →̇ ψ ∈? e Γ n }) (e Γ n ⨉ enum n))
    {- AllI -}   ++ map ∀̇_ (e (⭡ Γ) n)
    {- AllE -}   ++ map (λ { (φ , t) → φ [ t ]₀ }) (filter (λ { (φ , _) → ∀̇ φ ∈? e Γ n }) (enum n ⨉ enum n))
    {- FalseE -} ++ filter (λ _ → ⊥̇ ∈? e Γ n) (enum n)
    {- Peirce -} ++ map (λ { (φ , ψ) → ((φ →̇ ψ) →̇ φ) →̇ φ }) (enum n ⨉ enum n)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/ProofEnumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.ProofEnumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.proof-enumeration)  
> 交流Q群: 893531731
