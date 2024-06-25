-- Exploring how to specify configuration of a model (a System) in order to write the Dstep and Estep functions.

module Experiment1 where

open import Niche
open import Function.Base
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base -- using (_×_; _,′_) -- Needs stdlib 2.0
open import Agda.Builtin.Sigma
open import Agda.Builtin.Maybe


-- See docs/DunlinStory1.md for the rationale for the names and type constructors
-- or record fields below.

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

-----------------------------------------------------------
-- How to make collections of dunlins or envs, given that
-- each has a different type?  Answer #1: Sigma pairs.

--------------
-- Represent dependence on two parameters by dependence on a (non-dependent) pair
-- (more more generally, a non-dependent tuple).

-- pair-to-dun : (tuple : Σ ℕ (λ v → ℕ)) → Set  -- literal version of next line
pair-to-dun : Σ[ _ ∈ ℕ ] ℕ → Set  -- That's the nondep pair type syntax from Data.Product.Base
pair-to-dun tuple = Dun (fst tuple) (snd tuple)

-- abbreviate the type we need list elements to have
DunTuple : Set
DunTuple = Σ (ℕ × ℕ) pair-to-dun

beak-tuple : ((id env : ℕ) → Dun id env) → ℕ → ℕ → DunTuple
beak-tuple dun-structor id env = (id ,′ env) , dun-structor id env

-- This process can be automated
sara-tuple = beak-tuple thin-beak 3 4
elsbeth-tuple = beak-tuple thick-beak 6 6
bill-tuple = beak-tuple thin-beak 5 6
dunlin-tuples = sara-tuple ∷ elsbeth-tuple ∷ bill-tuple ∷ []

-- kludge version of head for testing without Maybe
shrunken-head : {A : Set} → (default : A) → List A → A
shrunken-head default [] = default
shrunken-head default (x ∷ xs) = x

-- doesn't work:
-- shrunken-head {Dunlin} (thick-beak 0 0 0) dunlin-tuples


