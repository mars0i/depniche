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

{-
Which version below is better?

The signature of the element type DunDuple is easier to read than that of
DunTriple, but the signature of the function that constructs the triples
is simpler -- than the one that constructs pairs. More importantly, if
there are more than two parameters, then one just has to iteratively
extend the signature of the element type, whereas with the Duple version
it just gets more complicated.  So despite the nasty signature of
DunTriple, I think it's better.  (One could of course make a function
that constructed such a type for any n parameters (that have their own
types).  But I don't think that's worth the trouble for this application.)

On the other hand, extracting the actual dunlin (or env) from the Sigma structure
might be easier if there's just a single Sigma pair with an embedded
regular ntuple.
-}

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
