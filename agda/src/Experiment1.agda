-- Exploring how to specify configuration of a model (a System) in order to write the Dstep and Estep functions.

module Experiment1 where

open import Niche
open import Function.Base
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base using (_×_; _,′_) -- Needs stdlib 2.0
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
-- Version 1:
-- Represent dependence on two parameters by Sigma pair containing Sigma pair

-- Type abbrev: dependent pair whose second element contains a dependent pair.
DunTriple : Set
DunTriple = (Σ ℕ (λ i → Σ ℕ (λ e → Dun i e)))

-- DunTriple makers
-- Note sure how to avoid defining multiple functions, one for each constructor.
-- I don't seem to be able to use a constructor as an argument to a function.

-- First arg is a Dun constructor.  Next two are its parameters.
beak-triple : ((id env : ℕ) → Dun id env) → ℕ → ℕ → DunTriple
beak-triple dun-structor id env = id , env , dun-structor id env
-- comma is right-associative, so that's = (id , (env , (thin-beak id env)))


-- Collection of dunlins (embeded in "Σ triples):
dunlins : List DunTriple
dunlins = beak-triple thin-beak  0 0 ∷
          beak-triple thin-beak  1 0 ∷
          beak-triple thin-beak  2 1 ∷
          beak-triple thick-beak 3 1 ∷ []

-- Let's try to pull one out of the list:

-- The fact head returns a Maybe is kindof a pita for the moment.

just-dunlin-triple : Maybe DunTriple
just-dunlin-triple = head dunlins 

-- Well this is a KLUDGE.
extract-duntriple : Maybe DunTriple → DunTriple
extract-duntriple (just x) = x
extract-duntriple Nothing = 42 , 42 , thin-beak 42 42

dunlin-triple = extract-duntriple just-dunlin-triple

-- Here, finally, is the dunlin at beginning of the list of triples:
dunlin = snd (snd dunlin-triple)

{-
triple-to-dunlin : {i e : ℕ} → DunTriple → (Dun i e)
triple-to-dunlin dt = snd (snd dt)
-}
-- This doesn't work.  I think because just applying snd loses i and e
-- which were embedded in the triple.  Or maybe my signature is wrong--
-- I shouldn't bind i and e implicitly, since they're in the DunTriple.
-- Run C-c C-d and look at the type of dunlin.  It's
--     Dun (fst dunlin-triple) (fst (snd dunlin-triple))
-- although the value from C-c C-n is
--     thin-beak 0 0


--------------
-- Version 2:
-- Represent dependence on two parameters by dependence on a (non-dependent) pair

pair-to-dun : (pr : Σ ℕ (λ v → ℕ)) → Set  -- had to read this off of C-c C-d
pair-to-dun = (λ pr → Dun (fst pr) (snd pr))

DunDuple : Set
DunDuple = Σ (ℕ × ℕ) pair-to-dun

beak-duple : ((id env : ℕ) → Dun id env) → ℕ → ℕ → DunDuple
beak-duple dun-structor id env = (id ,′ env) , dun-structor id env


---------------------------
-- Things that didn't work:

---? There has to be a way to do the following. I don't know the right incantation.
---? NO: It can't work.  Not with regular lists.  (?)
---? Example: dunlin-friends = sara ∷ elsbeth ∷ bill ∷ []  -- 6 != 3 of type ℕ (because elsbeth doesn't have sara's type Dun 3 4)

-- dunlins : List (Dun ℕ ℕ)  -- Set !=< ℕ
-- dunlins : List (Dun _ _) -- checks but only for the first element in list
-- dunlins : List (Dun i j) -- i is not in scope
-- dunlins : {i j : ℕ} → List (Dun i j) -- checks but then first element fails: zero != i of type ℕ

-- Trying to apply this
-- https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Collection.20of.20indexed.20type.20with.20different.20indexes.3F/near/446454518:
-- to multiple indexes:
-- dunlins = (0 , (λ i → (0 , (λ e → thin-beak i e)))) ∷ []

{-
dunlins = (thin-beak  0 0) ∷
          (thin-beak  1 0) ∷
          (thin-beak  2 1) ∷
          (thick-beak 3 1) ∷ []

environments : {i j : ℕ} → List (Env i (List j))
environments = (undisturbed 0 (0 ∷ 1 ∷ [])) ∷
               (undisturbed 1 (2 ∷ 3 ∷ [])) ∷ []
-}
-- Note that the indexes in these two lists are supposed to be
-- carefully kept in sync.  This is why I wanted to initialize using
-- DunEnvsAssocs.  Dstep and Estep have to keep them in sync, too, though.
-- Or store the indexes wholly in a DunEnvsAssocs.

