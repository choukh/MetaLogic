---
url: fol.syntax.proof-enumeration
---

# 一阶逻辑 ▸ 语法 ▸⁻ 证明的枚举

```agda
{-# OPTIONS --lossy-unification #-}
open import Foundation.Essential
open import FOL.Language.Base

module FOL.Syntax.ProofEnumeration (ℒ : Language) where
open import FOL.Syntax.Base ℒ
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
    {- ImpI -} ++ concat (map (λ φ → map (φ →̇_) (e (φ ∷ Γ) n)) (enum n))
    {- ImpE -} ++ map snd (filter {P = λ { (φ , ψ) → φ →̇ ψ ∈͆ e Γ n }} (λ x → {!  !}) (e Γ n ⨉ enum n))
    {- AllI -} ++ {!   !}
    {- AllE -} ++ {!   !}
    {- FalseE -} ++ {!   !}
    {- Peirce -} ++ {!   !}
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/ProofEnumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.ProofEnumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.proof-enumeration)  
> 交流Q群: 893531731
