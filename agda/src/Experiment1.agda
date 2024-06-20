-- Exploring how to specify configuration of a model (a System) in order to write the Dstep and Estep functions.

module Experiment1 where

open import Niche
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Dunlins and environments are indexed by id numbers:

-- These correspond to the D and E defs in Niche.Example:

data Dun : ℕ → Set where
  dun : (i : ℕ) → Dun i

data Env : ℕ → Set where
  env : (i : ℕ) → Env i

----------
-- Define data structure for initial set of relationships between dunlins and their environments

-- FIXME: What I did below is backwards.  I assigned possibly multiple envs to a dunlin, but I want to
-- have multiple envs per dunlin, and at this point not necessarily multiple envs per dunlin.

-- But there can be empty envs, i.e. with no dunlins.  So add a Maybe in the next definition?
DunIdx : Set
DunIdx = ℕ

-- There can't be environment-less dunlins, so no need to add Maybe:
EnvIdxs : Set
EnvIdxs = List ℕ

-- a "record" that records a bidirectional mapping between dunlins and envs
data DunEnvsPair : DunIdx → EnvIdxs → Set where
  dun-in-envs : (dun-idx : DunIdx) → (env-idxs : EnvIdxs) → DunEnvsPair dun-idx env-idxs

-- Now we need a bunch of these to store configuration of a model:


---? Not sure how to write this type.  This version checks, but I don't think it's right.
---? The implict vars are just placeholders for the contents of dun-idxes and env-idxs-list, respectively).
dun-env-pairs : {dun-idx : DunIdx} → {env-idxs : EnvIdxs} → (dun-idxs : List DunIdx) → (env-idxs-list : List EnvIdxs) → List (DunEnvsPair dun-idx env-idxs)
dun-env-pairs dun-idxs [] = [] -- If there are no environments, there can't be any dunlins.
dun-env-pairs [] (js ∷ env-idxs-list) = {!!}
dun-env-pairs (i ∷ dun-idxs) (js ∷ env-idxs-list) = {!!}

