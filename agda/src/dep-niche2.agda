module dep-niche2 where

open import nat
open import integer
open import string
open import vector
open import list

data Niche : (idx : ℕ) -> Set where
  MkNiche : (idx : ℕ) -> Niche idx

niche0 : Niche 0
niche0 = MkNiche 0

niche1 : Niche 1
niche1 = MkNiche 1

niches : List (Niche 0)
niches = [(MkNiche 0)]
