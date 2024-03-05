-- Can I work around the fact that Agda doesn't have type-case in
-- a simple way by using dependent pairs?
-- (cf. ../../Idris/src/DepPair.idr)
-- tldr: No, apparently.
module deppair where

-- open import nat -- ial

open import Agda.Builtin.Sigma
open import Data.Nat -- standard library

-- for preliminary examples
open import Data.Vec -- standard library
open import Data.String -- standard library


data Niche : (k : ℕ) → Set where
  User : (k : ℕ) → Niche k

-- Increment the index of an organism; new organism has a different niche.
incuser : {k : ℕ} → Niche k → Niche (suc k)
incuser (User k) = User (suc k)


xs : Vec String 2
xs = "this" ∷ "that" ∷ []

-- Dep pair usage illustration:
-- In the type, Σ takes two args separated by spaces, while in the instance,
-- comma is an infix operator (which must be surrounded by spaces in Agda).
xp : Σ ℕ (Vec String)  -- note (Vec String) is in effect a Curried fn with a Nat arg
xp = 2 , xs

-- User-level dependent pair
up : Σ ℕ Niche    -- By leaving out the ℕ arg to Niche, it's treated as a function of that arg
up = 2 , User 2   -- Note we use Niche above but its constructor here


-- There is no reason for this since incuser works.  It's an experiment.
incUserPair : Σ ℕ Niche → Σ ℕ Niche
incUserPair (k , User k) = (suc k) , User (suc k)

-- I can make a dependent pair at the Set level!  (As I would put it.)
np : Σ ℕ (λ n → Set)
np = 2 , Niche 2


{-
This fails because it doesn't like Niche k in the 2nd line:
incNichePair : Σ ℕ (λ n → Set) → Σ ℕ (λ n → Set)
incNichePair (k , Niche k) = (suc k) , Niche (suc k)
-}

-- This works!
incNichePair : Σ ℕ (λ n → Set) → Σ ℕ (λ n → Set)
incNichePair np = let k = (fst np) in
                  (suc k) , Niche (suc k)
