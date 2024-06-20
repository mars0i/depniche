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


------------------------------------------------------------
-- Define data structure for initial set of relationships between dunlins and their environments

---------------------------
-- Simplistic:

record DunEnvsPair : Set where
  field
    dunidx : ℕ
    envidxs : List ℕ

DunEnvsAssocs : Set
DunEnvsAssocs = List DunEnvsPair

-- That's supposed to be used to initialize a system, but
-- I haven't thought through the next steps.
