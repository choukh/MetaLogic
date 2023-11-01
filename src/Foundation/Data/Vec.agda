module Foundation.Data.Vec where

open import Data.Vec public
  using ([]; _∷_)
  renaming (Vec to 𝕍; map to map⃗)

open import Data.Vec.Properties public
  using (map-∘)


