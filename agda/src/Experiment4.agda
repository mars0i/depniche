-- Exploring how to specify configuration of a model (a System) in order to write the Dstep and Estep functions.

module Experiment4 where

open import Niche
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

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
-- Dun and Env records
-- These sort of correspond to the D and E defs in Niche.Example.

-- Note that the env and dunlins parameters are not Env or Dun;
-- they are id numbers.

data Beak : Set where
  thin : Beak
  thick : Beak

data Mud : Set where
  undisturbed : Mud
  mildly-disturbed : Mud
  well-disturbed : Mud

-- See
-- https://agda.readthedocs.io/en/latest/language/mutual-recursion.html#mutual-recursion-forward-declaration

record Dun : Set
record Env : Set

record Dun where
  field
    id : ℕ
    beak : Beak
    env-id : ℕ

record Env where
  field
    id : ℕ
    mud : Mud
    dunlin-ids : List ℕ

elsbeth = record {id = 0; beak = thin; env-id = 0}
emma    = record {id = 1; beak = thick; env-id = 1}
dex     = record {id = 2; beak = thin; env-id = 1}

west = record {id = 0; mud = mildly-disturbed; dunlin-ids = [ 0 ]}
east = record {id = 1; mud = undisturbed; dunlin-ids = 1 ∷ 2 ∷ []}

dunlins = elsbeth ∷ emma ∷ dex ∷ []
envs = west ∷ east ∷ []

----------------------

{-
Dun-dec≡ : Dec≡ Dun
Dun-dec≡ record { id = id₁ ; beak = beak₁ ; env-id = env-id₁ }
         record { id = id ; beak = beak ; env-id = env-id } = {!!}
-}
