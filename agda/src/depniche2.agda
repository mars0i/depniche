module depniche2

open import nat
open import integer
open import string
open import vector
open import list

-- Is this the right syntax? This is Idris syntax.  Seems to work.
data Niche : (idx : ℕ) → Set₂ where
  MkNiche : (idx : ℕ) → Niche idx

-- Doesn't work:
-- data Niche (idx : ℕ) : Set where
--   MkNiche : idx → Niche idx

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
nums2 = 2 :: 1 :: []



niches : 𝕃 Set₁
niches = Niche 0 :: Niche 1 :: Niche 2 :: []

-- doesn't work
-- incniche : {x : ℕ} → Set₁ → Set₁
-- incniche (Niche x) = Niche (suc x)
