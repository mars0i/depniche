module depniche3 where

open import nat
open import Agda.Primitive

data Niche : ∀ (k : ℕ) → Set where
  MkOrg : (k : ℕ) → Niche k

-- increment the index of an organism (an instance of Niche k)
incorganism : ∀ {k : ℕ} → Niche k → Niche (suc k)
incorganism (MkOrg k) = MkOrg (suc k)

org : Niche 7
org = MkOrg 7

niche : Set
niche = Niche 8

org2 : niche
org2 = incorganism org


{-
-- Doesn't check
incNiche : ∀ {k : ℕ} → Set → Set
incNiche (Niche k) = ?  -- parse error on (Niche k)
-- incNiche .(Niche k) = ?  -- Seems to parse but k is not in scope
-- incNiche {k} .(Niche k) = ?  -- Seems to say Niche k does not have type Set
-}


data Niche2 : ∀ (k : ℕ) → Set₁ where
  Niche1 : (k : ℕ) → Niche2 k

-- I can do this, and I think that Niche1 is in some sense
-- at the Set level [??] but it doesn't make Niche1
-- into the type of something lower.

nichey : Niche2 5
nichey = Niche1 5

incNiche1 : ∀ {k : ℕ} → Niche2 k → Niche2 (suc k)
incNiche1 (Niche1 k) = Niche1 (suc k)

nicheyest : Niche2 6
nicheyest = incNiche1 nichey
