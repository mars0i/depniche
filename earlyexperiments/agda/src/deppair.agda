-- Can I work around the fact that Agda doesn't have type-case in
-- a simple way by using dependent pairs?

-- It looks like you can do it.  But it's not pretty
-- (esp. in Agda, where the standard lib's dependent pair
-- syntax is kind of awful, if you ask me.

module deppair where

-- open import nat -- ial
open import Agda.Builtin.Sigma
open import Data.Nat -- standard library
-- open import Data.List

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
np0 : Σ ℕ (λ n → Set)
np0 = 0 , Niche 0

-- Helper for declaring niche pairs to make the definitions less messy looking.
-- Doesn't seem to work, so going back to lambdas.
-- setter : ℕ → Set
-- setter k = Niche k

-- How to make more
mkNichePair : ℕ → (Σ ℕ (λ n → Set))
mkNichePair k = k , Niche k

-- Increment a niche's index.  (Using a dependent pair works!)
incNichePair : Σ ℕ (λ n → Set) → Σ ℕ (λ n → Set)
incNichePair np = let k = (fst np) in
                  (suc k) , Niche (suc k)

np1 : Σ ℕ (λ n → Set)
np1 = mkNichePair 1

np2 : Σ ℕ (λ n → Set)
np2 = incNichePair np1

-- Works because the different Niches, though they are different
-- types, all have the same type.
nps : Vec (Σ ℕ (λ n → Set)) 3
nps = np0 ∷ np1 ∷ np2 ∷ []

nps+ : Vec (Σ ℕ (λ n → Set)) 3
nps+ = map incNichePair nps
