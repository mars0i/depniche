

open import nat
open import integer
open import string
open import vector
open import list

data Niche : (idx : ℕ) -> Set₁ where
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
nums2 = 2 :: 1 :: []



niches : 𝕃 Set₁
niches = Niche 0 :: Niche 1 :: Niche 2 :: []

-- not working:
-- inctype : ∀ {x : ℕ} -> Niche x -> Niche (suc x)
-- inctype : ∀ {x : ℕ} → Set₁ → Set₁
-- inctype {x} (Niche x) = Niche (suc x)
