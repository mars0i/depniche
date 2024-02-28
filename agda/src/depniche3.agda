module depniche3 where

open import nat

data Niche : ∀ (k : ℕ) → Set where
  MkOrg : (k : ℕ) → Niche k

incorganism : ∀ {k : ℕ} → (Niche k) → (Niche (suc k))
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
incNiche {k} .(Niche k) = ?  -- Seems to say Niche k does not have type Set
-- incNiche .(Niche k) = ?  -- Seems to parse but k is not in scope
-- incNiche (Niche k) = ?  -- parse error on (Niche k)
-}
