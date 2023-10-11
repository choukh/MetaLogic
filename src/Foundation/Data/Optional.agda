module Foundation.Data.Optional where

open import Data.Maybe public
  using ()
  renaming (Maybe to _？; nothing to none; just to some)
