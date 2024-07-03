-- Exploring how to specify configuration of a model (a System) in
-- order to write the Dstep and Estep functions.

-- See docs/DunlinStory1.md for the rationale for the names and type constructors
-- or record fields below.

module DunlinsEnvs where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Maybe
open import Function.Base
open import Data.List
open import Data.Vec as V using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base -- using (_×_; _,′_) -- Needs stdlib 2.0
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Niche
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
  short-beak   : (id : ℕ) → (env : ℕ) → Dun id env
  long-beak  : (id : ℕ) → (env : ℕ) → Dun id env

-- An abbreviation for the type of the Dun constructors will be useful later.
DunConstructor : Set 
DunConstructor = (i : ℕ) → (e : ℕ) → Dun i e


data Env : ℕ → List ℕ → Set where
  undisturbed      : (id : ℕ) → (dunlins : List ℕ) → Env id dunlins
  mildly-disturbed : (id : ℕ) → (dunlins : List ℕ) → Env id dunlins
  well-disturbed   : (id : ℕ) → (dunlins : List ℕ) → Env id dunlins

-- An abbreviation for the type of the Env constructors will be useful later.
EnvConstructor : Set
EnvConstructor = (i : ℕ) → (ds : List ℕ) → Env i ds

-----------------------------------------------------------
-- How to make collections of dunlins or envs, given that
-- each has a different type?  Answer #1: Sigma pairs.

-- Represent dependence on two parameters by dependence on a (non-dependent) pair
-- (more more generally, a non-dependent tuple).

-- abbreviate the type we need list elements to have
DunPair : Set
DunPair = Σ (ℕ × ℕ) (λ (id , env-id) → Dun id env-id) -- comma pattern match in lambda

DunPairList : Set
DunPairList = List DunPair

make-dun-pair : ((id env : ℕ) → Dun id env) → ℕ → ℕ → DunPair
make-dun-pair structor id env = (id ,′ env) , structor id env

-- kinda backwards: we deconstruct a dunlin in order to recreate it in a Σ-type
-- Seems potentially useful.
dun-to-pair : {id env : ℕ} → Dun id env → DunPair
dun-to-pair (short-beak id env)  = make-dun-pair short-beak id env
dun-to-pair (long-beak id env) = make-dun-pair long-beak id env


{-
sara-tuple = make-dun-pair short-beak 3 4
elsbeth-tuple = make-dun-pair long-beak 6 6
bill-tuple = dun-to-pair (short-beak 5 6)

flock = sara-tuple ∷ elsbeth-tuple ∷ bill-tuple ∷ []
sara = snd (dunlin-head flock)
elsbeth = snd (dunlin-head (dunlin-tail flock))
bill = snd (dunlin-head (dunlin-tail (dunlin-tail flock)))
-}

------------------------------------------------------------

-- abbreviate the type we need list elements to have
EnvPair : Set
EnvPair = Σ (ℕ × List ℕ) (λ (id , dun-ids) → Env id dun-ids)

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
default-dun-tuple = make-dun-pair short-beak 1000 1000
dun-head = exploding-head default-dun-tuple
dun-tail = exploding-tail default-dun-tuple
default-env-tuple = make-env-pair undisturbed 1000 [ 1000 ]
env-head = exploding-head default-env-tuple
env-tail = exploding-tail default-env-tuple

-----------------------------
-- Configuring an entire system
-- I guess another way to do it would be to pair the dunlin ids and constructors

-- in a single embedded list.
DunEnvAssocs : Set
DunEnvAssocs = List ((List ℕ × List DunConstructor) × (ℕ × EnvConstructor))


-- Less efficient to run through the config list twice, but it's simpler
-- and shouldn't take long.

---------
-- Create the environments from a DunEnvAssocs list.

-- Creates a list of environment Sigma-pairs from the assocs.
assocs-to-envs : DunEnvAssocs → List EnvPair
assocs-to-envs [] = []
assocs-to-envs (x ∷ xs) = let ((dun-ids , _) , (env-id , env-maker)) = x
                          in (make-env-pair env-maker env-id dun-ids) ∷ assocs-to-envs xs

---------
-- Create the dunlins from a DunEnvAssocs list.

-- Helper function for assocs-to-dunlists. Assumes the two arg lists are same length.
-- Strictly speaking ought to be Maybe-ed, or use vectors or add a length proof. (TODO?)
duns-for-env : ℕ → List ℕ → List DunConstructor → List DunPair
duns-for-env env-id [] [] = []
duns-for-env env-id (id ∷ dun-ids) (maker ∷ dun-makers) =
    let dun-pair = make-dun-pair maker id env-id
    in dun-pair ∷ duns-for-env env-id dun-ids dun-makers
duns-for-env _ _ _ = [] -- This shouldn't happen, but if it does, it's a bug.
                    
-- Helper for assocs-to-duns, which flattens this list list.
assocs-to-dunlists : DunEnvAssocs → List (List DunPair)
assocs-to-dunlists [] = []
assocs-to-dunlists (x ∷ xs) =
    let ((dun-ids , dun-makers) , (env-id , _)) = x
    in (duns-for-env env-id dun-ids dun-makers) ∷ assocs-to-dunlists xs

-- Creates a list of dunlin Sigma-pairs from the assocs.
assocs-to-duns : DunEnvAssocs → List DunPair
assocs-to-duns assocs = concat (assocs-to-dunlists assocs)


-- Example:

-- Note that without the type sig, the commas have to be comma-ticks;
-- with the sig, commas are OK.
dun-env-assocs : DunEnvAssocs
dun-env-assocs = ((3 ∷ 4 ∷ [] , short-beak ∷ short-beak ∷ []) , (0 , mildly-disturbed)) ∷
                 (([ 1 ] , [ short-beak ]) , (1 , undisturbed)) ∷
                 (([ 2 ] , [ long-beak ]) , (2 , mildly-disturbed)) ∷
                 (([ 5 ] , [ long-beak ]) , (3 , well-disturbed)) ∷
                 []

-- The first element of each top level pairs in these lists is just there
-- to allow different types to live in the same list.  When processing
-- the envs or dunlins, it can be ignored (but might need to be recreated to
-- make the next set of envs and dunlins.
envpairs = assocs-to-envs dun-env-assocs
dunpairs = assocs-to-duns dun-env-assocs

-- Testing--throw away the first element of top-level pairs:
an-env = snd (env-head envpairs)
a-dun = snd (dun-head dunpairs)
another-dun = snd (dun-head (dun-tail dunpairs))
