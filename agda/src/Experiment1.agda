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

-- kinda backwards: we deconstruct a dunlin in order to recreate it in a Σ-type
dunlin-to-tuple : {id env : ℕ} → Dun id env → DunTuple
dunlin-to-tuple (thin-beak id env)   = beak-tuple thin-beak id env
dunlin-to-tuple (thick-beak id env) = beak-tuple thick-beak id env



-- This process can be automated
sara-tuple = beak-tuple thin-beak 3 4
elsbeth-tuple = beak-tuple thick-beak 6 6
bill-tuple = dunlin-to-tuple (thin-beak 5 6)

dunlin-tuples = sara-tuple ∷ elsbeth-tuple ∷ bill-tuple ∷ []

default-dunlin = thin-beak 0 0
default-dunlin-tuple = (dunlin-to-tuple default-dunlin)

-- kludge version of head for testing without Maybe
shrunken-head : {A : Set} → (default : A) → List A → A
shrunken-head default [] = default
shrunken-head default (x ∷ xs) = x

-- Needs to be rewritten properly with Maybe
dunlin-head : {id env : ℕ} → List DunTuple → (Dun id env)
dunlin-head xs = let head-tuple = shrunken-head default-dunlin-tuple xs
                 in {!!} -- snd head-tuple  -- doesn't work
{-
Goal: Dun id₁ env
————————————————————————————————————————————————————————————
head-tuple
    : Σ (ℕ × ℕ) pair-to-dun
head-tuple
    = shrunken-head default-dunlin-tuple xs
xs  : List DunTuple
env : ℕ   (not in scope)
id₁ : ℕ   (not in scope)
-}

first-dunlin-tuple = shrunken-head default-dunlin-tuple dunlin-tuples

-- Doesn't work, but 'C-c C-n snd first-dunlin-tuple' does.
-- sara-again = snd first-dunlin-tuple




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
