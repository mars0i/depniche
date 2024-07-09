module Model1 where

-- See docs/DunlinStory1.md for rationale for names, data, etc.

{- General notes on code

After looking at the Example module in Niche.agda, I wanted to do
something slightly more involved  with the dunlin and enviorment
types in order to implement the transition rules Dstep and Estep.
I wasn't sure how to fill in the holes you left in the e-evolve
function; I needed a story to motivate the rules, and that meant
changing the dunlin and environment types.

I'm not sure if the way I did this is a good idea, and it doesn't
quite fit what I'd originally envisioned (which may be a bad idea
anyway).  I just wanted to get something working, and it was a
learning experience, but I may have gone down a bad path, or I
might have made poor choices within a good path. So I have no
problem with this being revised or completely rethought and
rewritten from scratch.

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

--------

-- Each dunlin should have a unique id, and a location loc, which is an id
-- for the dunlin's current environment.  (It could be the env itself, but
-- I couldn't figure out how to do this kind of mutual recursion.)
data Dun : Set where
  short-beak   : (id : ℕ) → (loc : ℕ) → Dun
  long-beak  : (id : ℕ) → (loc : ℕ) → Dun

-- An abbreviation for the type of the Dun constructors will be useful later.
DunConstr : Set 
DunConstr = (i : ℕ) → (e : ℕ) → Dun

-- Urgh.  To generate new ids in the natural way (incrementing the last
-- one stored in a global), dunlin creation would have to be done in a
-- state monad or something like that.

-- Make a new dunlin using the provided constructor, creating a new id by
-- incrementing the previous max id that should be passed in.  The new id
-- can be extracted from the new dunlin as the new max id.
new-dunlin : (max-id : ℕ) → DunConstr → (env-id : ℕ) → Dun
new-dunlin max-id constr env-id = constr (suc max-id) env-id

--------

-- Environments have a location loc, which is a unique id and also specifies
-- which environments are adjacent (e.g. env 5 is next to envs 4 and 6).
-- Environments also contain zero or more dunlins. Here we construct actual
-- dunlins rather than storing their ids.
data Env : Set where
  undisturbed      : (loc : ℕ) → (dunlins : List Dun) → Env
  mildly-disturbed : (loc : ℕ) → (dunlins : List Dun) → Env
  well-disturbed   : (loc : ℕ) → (dunlins : List Dun) → Env
-- In a future version, perhaps the level of disturbed-ness should captured by an
-- parameter rather than different constructors.  If it's an index, that captures
-- the idea that it's a different type, and it might require using lists or
-- vectors over sigma pairs (Σ ℕ (Env ℕ)) instead of Envs.  (See
-- learning/Model1indexedID.agda in commit #3f46335 for illustrations.)
-- Perhaps the location id should be a type index as well.

-- An abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = (i : ℕ) → (ds : List Dun) → Env

-- projection operators
env-params : Env → (ℕ × List Dun)
env-params (undisturbed loc dunlins) = (loc , dunlins)
env-params (mildly-disturbed loc dunlins) = (loc , dunlins)
env-params (well-disturbed loc dunlins) = (loc , dunlins)

-----------------------------
-- Configuring an entire system
-- I guess anothger way to do it would be to pair the dunlin ids and constructors

-- in a single embedded list.
DunEnvAssocs : Set
DunEnvAssocs = List ((List ℕ × List DunConstr) × (ℕ × EnvConstr)) 
--                    dun ids                     loc

---------
-- Create the environments from a DunEnvAssocs list.

-- Creates a list of environment Sigma-pairs from the assocs.
assocs-to-envs : DunEnvAssocs → List Env
assocs-to-envs [] = []
assocs-to-envs (x ∷ xs) = let ((dun-ids , dun-constrs) , (loc , env-constr)) = x
                              duns = zipWith (λ id constr → (constr id loc)) dun-ids dun-constrs
                          in (env-constr loc duns) ∷ assocs-to-envs xs

---------
-- Create the dunlins from a DunEnvAssocs list.

-- Helper function for assocs-to-dunlists. Assumes the two arg lists are same length.
-- Strictly speaking ought to be Maybe-ed, or use vectors or add a length proof. (TODO?)
duns-for-env : ℕ → List ℕ → List DunConstr → List Dun
duns-for-env loc [] [] = []
duns-for-env loc (id ∷ dun-ids) (constr ∷ dun-constrs) =
    let dun-pair = constr id loc
    in dun-pair ∷ duns-for-env loc dun-ids dun-constrs
duns-for-env _ _ _ = [] -- This shouldn't happen, but if it does, it's a bug.
                    
-- Helper for assocs-to-duns, which flattens this list list.
assocs-to-dunlists : DunEnvAssocs → List (List Dun)
assocs-to-dunlists [] = []
assocs-to-dunlists (x ∷ xs) =
    let ((dun-ids , dun-constrs) , (loc , _)) = x
    in (duns-for-env loc dun-ids dun-constrs) ∷ assocs-to-dunlists xs

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
get-fitness : {dun-id loc : ℕ} → {dun-ids : List ℕ} → Dun → Env → Fitness
get-fitness (short-beak _ _) (undisturbed _ _)      = 0
get-fitness (short-beak _ _) (mildly-disturbed _ _) = 1
get-fitness (short-beak _ _) (well-disturbed _ _)   = 2
get-fitness (long-beak _ _)  (undisturbed _ _)      = 2
get-fitness (long-beak _ _)  (mildly-disturbed _ _) = 1
get-fitness (long-beak _ _)  (well-disturbed _ _)   = 0

offspring : Dun → Env → List Dun
offspring (short-beak id loc) env = {!!} -- NEED unique-id creator. get fitness, create dunlins
offspring (long-beak  id loc) env = {!!} -- Can use List.Base.iterate (no repeat since need new id)


-- Original example in Niche.agda also had a timestep parameter, but 
-- the transition rules can be the same at every time.
-- Since each env contains a list of dunlins in it, an option might be
-- to iterate through the env list, and ignore the dunlin list.

-- Since this model stores dunlins inside environments, we can update the dunlins
-- by iterating through the envs.  There are several things might occur:
--   Determine each dunlin's fitness
--   Create new dunlins as a response, and place them in some environments.
--   Change state of environments in response to niche construction by dunlins.
--   Possibly change state of environments in response to states of neighboring envs.
--   Allow old dunlins to move to adjacent environments.
-- These need not all be done by d-evolve.  Callan's idea of modifying
-- dunlins and envs separately is a good idea.
-- max-dun-id is the previous maximum dunlin-id, which should be passed to new-dunlin,
-- which will increment it.
d-evolve : (max-dun-id : ℕ) → (Eₜ : List Env) → List Env
d-evolve max-id [] = []
d-evolve max-id (e ∷ es) = let (loc , dunlins) = env-params e
                           in {!!}



-- old notes:
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
 
