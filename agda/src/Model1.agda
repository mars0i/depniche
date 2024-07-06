module Model1 where

-- See docs/DunlinStory1.md for rationale for names, data, etc.

{- General notes on code

After looking at the Example module in Niche.agda, I wanted to do
something slightly more involved  with the dunlin and enviorment
types in order to implement the transition rules Dstep and Estep.
I wasn't sure how to fill in the holes you left in the e-evolve
function; I needed a story to motivate the rules, and that meant
changing the dunlin and environment types.

I'm not sure if the way I did this is a good idea.  I just wanted
to get something working, and it was a learning experience, but
I may have gone down a bad path, or I might have made poor choices
within a good path.

I have no problem with this being revised or completely rethought
and rewritten from scratch.

Also, there is a configuration structure, DunEnvAssocs, that the
code  uses initialize a system.  This is just some collections of
Nats.  Not sure whether that's the way to go.

-}

-- open import Agda.Builtin.Sigma
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

data Dun : Set where
  short-beak   : (id : ℕ) → (env : ℕ) → Dun
  long-beak  : (id : ℕ) → (env : ℕ) → Dun

-- An abbreviation for the type of the Dun constructors will be useful later.
DunConstr : Set 
DunConstr = (i : ℕ) → (e : ℕ) → Dun

data Env : Set where
  undisturbed      : (id : ℕ) → (dunlins : List ℕ) → Env
  mildly-disturbed : (id : ℕ) → (dunlins : List ℕ) → Env
  well-disturbed   : (id : ℕ) → (dunlins : List ℕ) → Env
-- In a future version, perhaps the level of disturbed-ness should captured by an
-- parameter rather than different constructors.  If it's an index, that captures
-- the idea that it's a different type, and it might require using lists or
-- vectors over sigma pairs (Σ ℕ (Env ℕ)) instead of Envs.  (See
-- learning/Model1indexedID.agda in commit #3f46335 for illustrations.)

-- An abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = (i : ℕ) → (ds : List ℕ) → Env

-----------------------------
-- Configuring an entire system
-- I guess another way to do it would be to pair the dunlin ids and constructors

-- in a single embedded list.
DunEnvAssocs : Set
DunEnvAssocs = List ((List ℕ × List DunConstr) × (ℕ × EnvConstr))

---------
-- Create the environments from a DunEnvAssocs list.

-- Creates a list of environment Sigma-pairs from the assocs.
assocs-to-envs : DunEnvAssocs → List Env
assocs-to-envs [] = []
assocs-to-envs (x ∷ xs) = let ((dun-ids , _) , (env-id , env-maker)) = x
                          in (env-maker env-id dun-ids) ∷ assocs-to-envs xs

---------
-- Create the dunlins from a DunEnvAssocs list.

-- Helper function for assocs-to-dunlists. Assumes the two arg lists are same length.
-- Strictly speaking ought to be Maybe-ed, or use vectors or add a length proof. (TODO?)
duns-for-env : ℕ → List ℕ → List DunConstr → List Dun
duns-for-env env-id [] [] = []
duns-for-env env-id (id ∷ dun-ids) (maker ∷ dun-makers) =
    let dun-pair = maker id env-id
    in dun-pair ∷ duns-for-env env-id dun-ids dun-makers
duns-for-env _ _ _ = [] -- This shouldn't happen, but if it does, it's a bug.
                    
-- Helper for assocs-to-duns, which flattens this list list.
assocs-to-dunlists : DunEnvAssocs → List (List Dun)
assocs-to-dunlists [] = []
assocs-to-dunlists (x ∷ xs) =
    let ((dun-ids , dun-makers) , (env-id , _)) = x
    in (duns-for-env env-id dun-ids dun-makers) ∷ assocs-to-dunlists xs

-- Creates a list of dunlin Sigma-pairs from the assocs.
assocs-to-duns : DunEnvAssocs → List Dun
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

{- (I wish Agda had a normal list and vector syntax.  I don't care if the number
of characters is the same as Haskell/OCaml/Idris/Lean. It's still harder to read.) -}


-- The first element of each top level pairs in these lists is just there
-- to allow different types to live in the same list.  When processing
-- the envs or dunlins, it can be ignored (but might need to be recreated to
-- make the next set of envs and dunlins.
envpairs = assocs-to-envs dun-env-assocs
dunpairs = assocs-to-duns dun-env-assocs

-----------------
-- Fitness and niche construction
-- IN PROGRESS

-- See docs/DunlinStory1.md for a sketch of possible rules to
-- use to implement `Dstep and `Estep in Niche.agda.

-- number of offspring for next generation
Fitness : Set
Fitness = ℕ

-- See docs/DunlinStory1.md for rationale, constraints
get-fitness : {dun-id env-id : ℕ} → {dun-ids : List ℕ} → Dun → Env → Fitness
get-fitness (short-beak _ _) (undisturbed _ _)      = 0
get-fitness (short-beak _ _) (mildly-disturbed _ _) = 1
get-fitness (short-beak _ _) (well-disturbed _ _)   = 2
get-fitness (long-beak _ _)  (undisturbed _ _)      = 2
get-fitness (long-beak _ _)  (mildly-disturbed _ _) = 1
get-fitness (long-beak _ _)  (well-disturbed _ _)   = 0

-- Original example in Niche.agda also had a timestep parameter, but 
-- the transition rules can be the same at every time.
-- Since each env contains a list of dunlins in it, an option might be
-- to iterate through the env list, and ignore the dunlin list.
d-evolve : (Eₜ : List Env) → (Dₜ : List Dun) → List Dun
d-evolve Eₜ = {!!}
-- for each env:
--   * Reconstruct the dunlins in it (possible since at present dunlins don't
--     have any data except the dunlin id and the env id, both of which are known
--     to the env).  Later we'll need to be able to look up dunlins by id, or
--     store the dunlins themselves in the env if there's a way to do that.
--     CONSIDER STORING DUNLINS IN ENVS, BUT ONLY ENV IDS IN DUNLINS.
--   * for each such dunlin:
--       - use get-fitness to return the fitnesses for each
--       - create fitness new dunlins of the same kind, and place them ... in some env,
--         updating the env in the dunlin (and in the envs? then need a different type)
--   * possibly kill some old dunlins
 
