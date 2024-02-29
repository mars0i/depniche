module depniche3 where

-- open import Agda.Primitive
open import Data.Nat -- standard library
-- open import nat -- ial

data Niche : (k : ℕ) → Set where
  NicheUser : (k : ℕ) → Niche k

-- Increment the index of an organism; new organism has a different niche.
incorganism : {k : ℕ} → Niche k → Niche (suc k)
incorganism (NicheUser k) = NicheUser (suc k)

{-
This won't work.  See
https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Pattern.20match.20on.20a.20type.20itself.3F/near/423871572
which also suggests a different strategy.

-- Increment index of a niche; new niche is different.
incNiche : {k : ℕ} → Set → Set
incNiche (Niche k) = ?  -- parse error on (Niche k)
incNiche _ = ?
-}

-- simple tests:

org : Niche 7
org = NicheUser 7

niche : Set
niche = Niche 8

org2 : niche
org2 = incorganism org


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

-- incNiche .(Niche k) = ?  -- Seems to parse but k is not in scope
-- incNiche {k} .(Niche k) = ?  -- Seems to say Niche k does not have type Set
