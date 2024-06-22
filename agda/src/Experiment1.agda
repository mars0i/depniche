-- Exploring how to specify configuration of a model (a System) in order to write the Dstep and Estep functions.

module Experiment1 where

open import Niche
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

{- 
  A speculative story I'm making up based on a couple of articles
  about dunlins or related birds: Depending on shape of beak,
  dunlins disturb mud more or less, which affects growth of small organisms
  that dunlins feed on or that become part of their gut microbiome.

  Is the following compatible with the structure in Callan's code in
  Niche.agda?  I think so.

  Every dunlin has an environment, identified by an environment id number.

  Every environment contains zero or more dunlins.

  Think of environment id numbers as simplified locations. At a given
  location, only one environment type is possible.  However, the type
  at that location can change.

  By contrast, dunlins have id numbers because every organism is unique.

  (Another environment difference that could be included is near-forest
  vs. far-from-forest.  Or maybe near-foliage, etc.  A dunlin can "construct"
  such an environment by choosing to build its nest there.  These differences
  can effect the probability of predation and protection from wind.)

  -MA

-}

----------------------------------------------------------
-- Dun and Env types
-- These correspond to the D and E defs in Niche.Example.

-- Note that the env and dunlins parameters are not Env or Dun;
-- they are id numbers.

data Dun : ℕ → ℕ → Set where
  thin-beak   : (id : ℕ) → (env : ℕ) → Dun id env
  thick-beak  : (id : ℕ) → (env : ℕ) → Dun id env

data Env : ℕ → List ℕ → Set where
  undisturbed      : (i : ℕ) → (dunlins : List ℕ) → Env i dunlins
  mildly-disturbed : (i : ℕ) → (dunlins : List ℕ) → Env i dunlins
  well-disturbed   : (i : ℕ) → (dunlins : List ℕ) → Env i dunlins


--------------------------
-- basic tests:

-- Can skip the type sig here:
sara = thin-beak 3 4

-- Or like this:
elsbeth : Dun _ _
elsbeth = thick-beak 6 6

-- Or use the type sig to fill in the indexes:
bill : Dun 5 6
bill = thick-beak _ _

north-sand = undisturbed 1 (5 ∷ 6 ∷ [])



------------------------------------------------------------
-- Define data structure for initial set of relationships between dunlins and their environments

---------------------------
-- Simplistic:


-- This is supposed to be used to initialize a system, but
-- I haven't thought through the next steps.
record DunEnvsPair : Set where
  field
    dunidx : ℕ
    envidxs : List ℕ

DunEnvsAssocs : Set
DunEnvsAssocs = List DunEnvsPair

---------------------------
-- Doing it by hand, without DunEnvsAssocs:

---? There has to be a way to do the following. I don't know the right incantation.
---? NO: It can't work.  Not with regular lists.  (?)
---? Example: dunlin-friends = sara ∷ elsbeth ∷ bill ∷ []  -- 6 != 3 of type ℕ (because elsbeth doesn't have sara's type Dun 3 4)

-- dunlins : List (Dun ℕ ℕ)  -- Set !=< ℕ
-- dunlins : List (Dun _ _) -- checks but only for the first element in list
-- dunlins : List (Dun i j) -- i is not in scope
dunlins : {i j : ℕ} → List (Dun i j) -- checks but then first element fails: zero != i of type ℕ
dunlins = (thin-beak  0 0) ∷
          (thin-beak  1 0) ∷
          (thin-beak  2 1) ∷
          (thick-beak 3 1) ∷ []

environments : {i j : ℕ} → List (Env i (List j))
environments = (undisturbed 0 (0 ∷ 1 ∷ [])) ∷
               (undisturbed 1 (2 ∷ 3 ∷ [])) ∷ []

-- Note that the indexes in these two lists are supposed to be
-- carefully kept in sync.  This is why I wanted to initialize using
-- DunEnvsAssocs.  Dstep and Estep have to keep them in sync, too, though.
-- Or store the indexes wholly in a DunEnvsAssocs.
