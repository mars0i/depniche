module depniche where

import Agda.Builtin.Nat


data Niche : (idx : Nat) → Set where
  MkNiche : (idx : Nat) → Niche idx
