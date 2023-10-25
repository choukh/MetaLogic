module FOL.Language where

open import Foundation.Essential

record Language : 𝕋₁ where
  field
    𝓕 : 𝕋
    𝓡 : 𝕋
    ∣_∣ᶠ : 𝓕 → ℕ
    ∣_∣ᴿ : 𝓡 → ℕ
    discr𝓕 : discrete 𝓕
    discr𝓡 : discrete 𝓡
    enum𝓕 : enumerable 𝓕
    enum𝓡 : enumerable 𝓡

  count𝓕 : countable 𝓕
  count𝓕 = discr→enum→count discr𝓕 enum𝓕

  count𝓡 : countable 𝓡
  count𝓡 = discr→enum→count discr𝓡 enum𝓡
