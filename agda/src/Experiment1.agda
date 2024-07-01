-- Exploring how to specify configuration of a model (a System) in
-- order to write the Dstep and Estep functions.

-- See docs/DunlinStory1.md for the rationale for the names and type constructors
-- or record fields below.

module Experiment1 where

open import Niche
open import Function.Base
open import Data.List
open import Data.Vec as V using (_∷_)
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
  undisturbed      : (id : ℕ) → (dunlins : List ℕ) → Env id dunlins
  mildly-disturbed : (id : ℕ) → (dunlins : List ℕ) → Env id dunlins
  well-disturbed   : (id : ℕ) → (dunlins : List ℕ) → Env id dunlins


-----------------------------------------------------------
-- How to make collections of dunlins or envs, given that
-- each has a different type?  Answer #1: Sigma pairs.

-- Represent dependence on two parameters by dependence on a (non-dependent) pair
-- (more more generally, a non-dependent tuple).

-- abbreviate the type we need list elements to have
DunPair : Set
DunPair = Σ (ℕ × ℕ) (λ prod → Dun (fst prod) (snd prod))

DunPairList : Set
DunPairList = List DunPair

make-dun-pair : ((id env : ℕ) → Dun id env) → ℕ → ℕ → DunPair
make-dun-pair structor id env = (id ,′ env) , structor id env

-- kinda backwards: we deconstruct a dunlin in order to recreate it in a Σ-type
-- Seems potentially useful.
dun-to-pair : {id env : ℕ} → Dun id env → DunPair
dun-to-pair (thin-beak id env)  = make-dun-pair thin-beak id env
dun-to-pair (thick-beak id env) = make-dun-pair thick-beak id env


{-
sara-tuple = make-dun-pair thin-beak 3 4
elsbeth-tuple = make-dun-pair thick-beak 6 6
bill-tuple = dun-to-pair (thin-beak 5 6)

flock = sara-tuple ∷ elsbeth-tuple ∷ bill-tuple ∷ []
sara = snd (dunlin-head flock)
elsbeth = snd (dunlin-head (dunlin-tail flock))
bill = snd (dunlin-head (dunlin-tail (dunlin-tail flock)))
-}

------------------------------------------------------------

-- abbreviate the type we need list elements to have
EnvPair : Set
EnvPair = Σ (ℕ × List ℕ) (λ prod → Env (fst prod) (snd prod))

EnvPairList : Set
EnvPairList = List EnvPair

make-env-pair : ((id : ℕ) (dunlins : List ℕ) → Env id dunlins) → ℕ → List ℕ → EnvPair
make-env-pair structor id dunlins = (id ,′ dunlins) , structor id dunlins

-- kinda backwards: we deconstruct a dunlin in order to recreate it in a Σ-type
-- Seems potentially useful.
env-to-pair : {id : ℕ} {dunlins : List ℕ} → Env id dunlins → EnvPair
env-to-pair (undisturbed id dunlins)  = make-env-pair undisturbed id dunlins
env-to-pair (mildly-disturbed id dunlins)  = make-env-pair mildly-disturbed id dunlins
env-to-pair (well-disturbed id dunlins)  = make-env-pair well-disturbed id dunlins

{-
envs = make-env-pair undisturbed 1 [ 1 ] ∷
       make-env-pair mildly-disturbed 2 (2 ∷ 3 ∷ [])∷
       env-to-pair (well-disturbed 3 []) ∷ []
-}

-----------------------------
-- For quick testing and experimentation.  Don't use for production code.
default-dun-tuple = make-dun-pair thin-beak 1000 1000
dun-head = exploding-head default-dun-tuple
dun-tail = exploding-tail default-dun-tuple
default-env-tuple = make-env-pair undisturbed 1000 [ 1000 ]
env-head = exploding-head default-env-tuple
env-tail = exploding-tail default-env-tuple

-----------------------------
-- Configuring an entire system

{-
For each env there are zero to many dunlins.
So we need to associate multiple dun ids with each env id.
We also need to specify which env and dun constructors go with each id.
We put the id relationships in a single list in order to keep the
dunlins and environments, which have to point to each other, consistent.

It might be better to do this with records rather than non-dep tuples.
I think that would work.

(Can't do it in any straightforward way with datatypes, because indexed
datatypes are different types and therefore can't appear in a list.)
-}


-- The structure of a list of configuration information for initializing a system.
-- The lengths of the two lists arguments should be the same.  So maybe should be
-- replaced by vectors, or add length proofs.
{-
DunEnvAssocs : Set
DunEnvAssocs = List (List ℕ ×                                -- dunlin ids for env
                     List ((i : ℕ) → (e : ℕ) → Dun i e) ×    -- dunlin constructors
                     ℕ ×                                     -- env id
                     ((i : ℕ) → (ds : List ℕ) → Env i ds) )  -- env constructor
-}

-- NO THIS IS NOT RIGHT.  It requires that each env has the same number of dunlins.
-- Also, breaks the functions below.
DunEnvAssocs : {n : ℕ} → Set
DunEnvAssocs {zero} = List (V.Vec ℕ zero × V.Vec ℕ zero × ℕ × ((i : ℕ) → (ds : List ℕ) → Env i ds) )
DunEnvAssocs {suc n} = List (V.Vec ℕ n ×                        -- dunlin ids for env
                       V.Vec ((i : ℕ) → (e : ℕ) → Dun i e) n ×  -- dunlin constructors
                       ℕ ×                                      -- env id
                       ((i : ℕ) → (ds : List ℕ) → Env i ds) )   -- env constructor

-- Less efficient to run through the config list twice, but it's a lot simpler,
-- and shouldn't take long.

---------
-- Create the environments from a DunEnvAssocs list.

-- Creates a list of environment Sigma-pairs from the assocs.
assocs-to-envs : DunEnvAssocs → List EnvPair
assocs-to-envs [] = []
assocs-to-envs (x ∷ xs) = let (dun-ids , _ , env-id , env-maker) = x
                          in (make-env-pair env-maker env-id (V.toList dun-ids)) ∷ assocs-to-envs xs

---------
-- Create the dunlins from a DunEnvAssocs list.

-- Helper function for assocs-to-dunlists. Assumes the two arg lists are same length.
-- Strictly speaking ought to be Maybe-ed, or use vectors or add a length proof. (TODO?)
duns-for-env : ℕ → List ℕ → List ((i : ℕ) → (e : ℕ) → Dun i e) → List DunPair
duns-for-env env-id [] [] = []
duns-for-env env-id (id ∷ dun-ids) (maker ∷ dun-makers) =
    let dun-pair = make-dun-pair maker id env-id
    in dun-pair ∷ duns-for-env env-id dun-ids dun-makers
duns-for-env _ _ _ = [] -- This shouldn't happen, but if it does, it's a bug.
                    
-- Helper for assocs-to-duns, which flattens this list list.
assocs-to-dunlists : DunEnvAssocs → List (List DunPair)
assocs-to-dunlists [] = []
assocs-to-dunlists (x ∷ xs) =
    let (dun-ids , dun-makers , env-id , _) = x
    in (duns-for-env env-id (V.toList dun-ids) (V.toList dun-makers)) ∷ assocs-to-dunlists xs

-- Creates a list of dunlin Sigma-pairs from the assocs.
assocs-to-duns : DunEnvAssocs → List DunPair
assocs-to-duns assocs = concat (assocs-to-dunlists assocs)


-- Example:

-- Note that without the type sig, the commas have to be comma-ticks;
-- with the sig, commas are OK.
dun-env-assocs : DunEnvAssocs
dun-env-assocs = ([ 1 ] , [ thin-beak ] , 0 , undisturbed) ∷
                 ([ 2 ] , [ thick-beak ] , 1 , mildly-disturbed) ∷
                 ([ 5 ] , [ thin-beak ] , 2 , mildly-disturbed) ∷
                 ([ 7 ] , [ thick-beak ] , 3 , well-disturbed) ∷
                 []

envpairs = assocs-to-envs dun-env-assocs
dunpairs = assocs-to-duns dun-env-assocs

{- testing:
a-dun = snd (dun-head dunpairs)
an-env = snd (env-head envpairs)
-}

