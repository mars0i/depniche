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

-- ial uses ::, but PLFA uses the character ∷ .
-- PLFA does this:
-- nums : List ℕ
-- nums = 1 ∷ []
-- ial:
nums : 𝕃 ℕ
nums = 1 :: []
-- or:
nums2 : list ℕ
nums2 = 1 :: []



-- niches : list (Set 0)
niches = [ (MkNiche 0) ]
