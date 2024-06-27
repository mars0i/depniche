-- Exploring how to specify configuration of a model (a System) in
-- order to write the Dstep and Estep functions.

-- See docs/DunlinStory1.md for the rationale for the names and type constructors
-- or record fields below.

module Experiment1 where

open import Niche
open import Function.Base
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base -- using (_×_; _,′_) -- Needs stdlib 2.0
open import Agda.Builtin.Sigma
open import Agda.Builtin.Maybe

open import Kludges

-- for primForce
-- open import Agda.Builtin.Strict


----------------------------------------------------------
-- Dun and Env types
-- These correspond to the D and E defs in Niche.Example.

-- Note that the env and dunlins parameters are not Env or Dun;
-- they are id numbers.  Maybe this can be changed, but I couldn't get
-- the mutual recursiou to work.

data Dun : ℕ → ℕ → Set where
  thin-beak   : (id : ℕ) → (env : ℕ) → Dun id env
  thick-beak  : (id : ℕ) → (env : ℕ) → Dun id env

data Env : ℕ → List ℕ → Set where
  undisturbed      : (i : ℕ) → (dunlins : List ℕ) → Env i dunlins
  mildly-disturbed : (i : ℕ) → (dunlins : List ℕ) → Env i dunlins
  well-disturbed   : (i : ℕ) → (dunlins : List ℕ) → Env i dunlins


-----------------------------------------------------------
-- How to make collections of dunlins or envs, given that
-- each has a different type?  Answer #1: Sigma pairs.

-- Represent dependence on two parameters by dependence on a (non-dependent) pair
-- (more more generally, a non-dependent tuple).

-- abbreviate the type we need list elements to have
DunPair : Set
DunPair = Σ (ℕ × ℕ) (λ prod → Dun (fst prod) (snd prod))

make-dun-pair : ((id env : ℕ) → Dun id env) → ℕ → ℕ → DunPair
make-dun-pair structor id env = (id ,′ env) , structor id env

-- kinda backwards: we deconstruct a dunlin in order to recreate it in a Σ-type
-- Seems potentially useful.
dunlin-to-pair : {id env : ℕ} → Dun id env → DunPair
dunlin-to-pair (thin-beak id env)  = make-dun-pair thin-beak id env
dunlin-to-pair (thick-beak id env) = make-dun-pair thick-beak id env

-- Just for quick testing and experimentation
default-dun-tuple = make-dun-pair thin-beak 1000 1000
dunlin-head = exploding-head default-dun-tuple
dunlin-tail = exploding-tail default-dun-tuple

{- Tests
sara-tuple = make-dun-pair thin-beak 3 4
elsbeth-tuple = make-dun-pair thick-beak 6 6
bill-tuple = dunlin-to-pair (thin-beak 5 6)
flock = sara-tuple ∷ elsbeth-tuple ∷ bill-tuple ∷ []
sara = snd (dunlin-head flock)
elsbeth = snd (dunlin-head (dunlin-tail flock))
bill = snd (dunlin-head (dunlin-tail (dunlin-tail flock)))
-}

------------------------------------------------------------



------------------------------------------------------------
-- Define data structure for initial set of relationships between
-- dunlins and their environments

-- This is supposed to be used to initialize a system, but
-- I haven't thought through the next steps.
record DunEnvsPair : Set where
  field
    dunidx : ℕ
    envidxs : List ℕ

DunEnvsAssocs : Set
DunEnvsAssocs = List DunEnvsPair
