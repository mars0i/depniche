module Model1a where
-- Like Model1 on 7/22/2024, but with Env indexed by locations.
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
-- open import Agda.Builtin.Maybe
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_)
open import Function.Base
open import Data.Bool
open import Data.List as L using (List; _∷_; []; [_]; iterate; _++_; map; concat; concatMap; zipWith; _[_]%=_; _[_]∷=_)
open import Data.Vec as V using (Vec; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base -- using (_×_; _,′_) -- Needs stdlib 2.0
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat.Properties using (<-strictTotalOrder)
import Data.Tree.AVL
open Data.Tree.AVL <-strictTotalOrder
open import Relation.Binary.PropositionalEquality -- for subst, at least

open import Niche
open import Kludges

-- for primForce
-- open import Agda.Builtin.Strict


----------------------------------------------------------
-- Dun and Env types
-- These correspond to the D and E defs in Niche.Example.

-- Overview of some choices:

-- Duns in an environment can be found from the Env they're in because
-- those Duns will be stored in a List (or Vec) in the Env.  (There may be
-- ways to store the Envs in the Duns as well, but the obvious ways lead
-- to nontermination, and I don't think it's the trouble.)

-- Duns have ids, but these are not indexes, to make it easier to store Duns
-- in a List in an Env.

-- Env ids are locations, and they are indexes.  This makes it esy
-- all Envs in a map in the form of an AVL tree, allowing lookup by location
-- from a Dun, and forcing envs at locations to be unique.

-- Dun ids should be unique as well--maybe it would be better to provide a
-- a lookup map for them too--but only to allow tracking of the states of
-- a dunlin over time.  This can be useful, even though it's not relevant
-- to evolution in a population.

-----------------------------------
-- Dunlins

-- Each dunlin should have a unique id, and a location loc, which is an id
-- for the dunlin's current environment.  (It could be the env itself, but
-- I couldn't figure out how to do this kind of mutual recursion.)
data Dun : Set where
  short-beak   : (id : ℕ) → (loc : ℕ) → Dun
  long-beak  : (id : ℕ) → (loc : ℕ) → Dun

-- An abbreviation for the type of the Dun constructors will be useful later.
DunConstr : Set 
DunConstr = (id : ℕ) → (loc : ℕ) → Dun

init-max-id : ℕ
init-max-id = 1

-- Make a new dunlin using the provided constructor, creating a new id by
-- incrementing the previous max id that should be passed in.  The new id
-- can be extracted from the new dunlin as the new max id.
new-dun : DunConstr → (max-id : ℕ) → (env-id : ℕ) → Dun
new-dun constr max-id env-id = constr (suc max-id) env-id

{-
-- For use inside List.iterate and similar functions to generate a
-- sequence of dunlins with consequitive (presumably new) ids.
next-dun : Dun → Dun
next-dun (short-beak id loc) = short-beak (suc id) loc
next-dun (long-beak id loc) = long-beak (suc id) loc
-}

-- projection operators
dun-params : Dun → (ℕ × ℕ)
dun-params (short-beak id loc) = (id , loc)
dun-params (long-beak id loc) = (id , loc)

dun-id : Dun → ℕ
dun-id (short-beak id _) = id 
dun-id (long-beak id _) = id

dun-loc : Dun → ℕ
dun-loc (short-beak _ loc) = loc 
dun-loc (long-beak _ loc) = loc

-- Is this non-idiomatic?
dun-constructor : Dun → DunConstr
dun-constructor (short-beak _ _) = short-beak
dun-constructor (long-beak _ _) = long-beak

-----------------------------------
-- Environments

-- Environments have a location loc, which is a unique id and also specifies
-- which environments are adjacent (e.g. env 5 is next to envs 4 and 6).
-- Environments also contain zero or more dunlins. Here we construct actual
-- dunlins rather than storing their ids.
data Env : ℕ → Set where
  undisturbed      : (dunlins : List Dun) → (loc : ℕ) → Env loc
  mildly-disturbed : (dunlins : List Dun) → (loc : ℕ) → Env loc
  well-disturbed   : (dunlins : List Dun) → (loc : ℕ) → Env loc
-- In a future version, perhaps the level of disturbed-ness should captured by an loc
-- parameter rather than different constructors.  If it's an index, that captures
-- the idea that it's a different type, and it might require using lists or
-- vectors over sigma pairs (Σ ℕ (Env ℕ)) instead of Envs.  (See
-- learning/Model1indexedID.agda in commit #3f46335 for illustrations.)
-- Perhaps the location id should be a type index as well.

-- An abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = (ds : List Dun) → (loc : ℕ) → Env loc

env-loc : {loc : ℕ} → Env loc → ℕ
env-loc (undisturbed _ loc) = loc
env-loc (mildly-disturbed _ loc) = loc
env-loc (well-disturbed _ loc) = loc

env-duns : {loc : ℕ} → Env loc → List Dun
env-duns (undisturbed dunlins _) = dunlins
env-duns (mildly-disturbed dunlins _) = dunlins
env-duns (well-disturbed dunlins _) = dunlins

-- Is this non-idiomatic?
env-constructor : {loc : ℕ} → Env loc → EnvConstr
env-constructor (undisturbed _ _) = undisturbed
env-constructor (mildly-disturbed _ _) = mildly-disturbed
env-constructor (well-disturbed _ _) = well-disturbed

-----------------------------
-- Create structure that stores envs, allows lookup by location,
-- enforces uniqueness wrt location.

-- This works because Env is indexed by loc.
EnvMap = Tree (MkValue Env (subst Env))

-- I still don't understand what's going on in MkValue, but it appears
-- that the first arg and the arg to subst should be an indexed datatype
-- (or a function?) where indexes are keys. i.e. this provides a map
-- from keys to values in which the keys are indexes of the value type.
-- (Data.Tree.AVL.IndexedMap provides a way to do somethng similar,
-- but I don't understand how to use it. To allow values to be
-- independent of keys use Data.Tree.AVL.Map.)

SysConfigInfo : Set
SysConfigInfo = List (ℕ × EnvConstr × List DunConstr)

system-config-info : SysConfigInfo
system-config-info =
  (1 , mildly-disturbed , (short-beak ∷ short-beak ∷ [])) ∷
  (2 , undisturbed , (short-beak ∷ [])) ∷ 
  (3 , mildly-disturbed , (long-beak ∷ [])) ∷
  (4 , well-disturbed , (long-beak ∷ [])) ∷
  []

new-duns-at-loc : (max-id : ℕ) → (loc : ℕ) → List DunConstr → List Dun
new-duns-at-loc _ _ [] = []
new-duns-at-loc max-id loc (constr ∷ constrs) =
  let new-id = suc max-id
  in (constr new-id loc) ∷ (new-duns-at-loc new-id loc constrs)

config-system : (max-id : ℕ) → SysConfigInfo → EnvMap → EnvMap
config-system _ [] _ = empty
config-system max-id (row ∷ more-rows) env-map =
  let (loc , env-constr , dun-constrs) = row
      duns = new-duns-at-loc init-max-id loc dun-constrs
      new-max-id = max-id + L.length duns
      new-env = env-constr duns loc
  in config-system new-max-id more-rows (insert loc new-env env-map)

-- Why is this generating empty?
all-envs : EnvMap
all-envs = config-system init-max-id system-config-info empty
-- check:
all-envs-list = toList all-envs

yo = new-duns-at-loc 0 1 (short-beak ∷ short-beak ∷ [])
lenyo = L.length yo
yo-env = mildly-disturbed yo 1
yo-map : EnvMap
yo-map = insert 1 yo-env empty
yo-map-size = size yo-map
yo-envs-list = toList yo-map


{-
dun-env-assocs =
((3 ∷ 4 ∷ [] , short-beak ∷ short-beak ∷ []) , (1 , mildly-disturbed)) ∷
(([ 1 ] , [ short-beak ]) , (2 , undisturbed)) ∷
(([ 2 ] , [ long-beak ]) , (3 , mildly-disturbed)) ∷
(([ 5 ] , [ long-beak ]) , (4 , well-disturbed)) ∷
[]
-}

-----------------------------
-- Configuring an entire system
-- I guess anothger way to do it would be to pair the dunlin ids and constructors

-- in a single embedded list.
DunEnvAssocs : Set
DunEnvAssocs = List ((List ℕ × List DunConstr) × (ℕ × EnvConstr)) 
--                    dun ids                     loc

---------
-- Create the environments from a DunEnvAssocs list.

{-
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

-- TEMPORARY KLUDGE: ENV 0 DOESN'T EXIST; IT INDICATES ERROR.  SO DON'T USE IT.
-- Note that without the type sig, the commas have to be comma-ticks;
-- with the sig, commas are OK.
dun-env-assocs : DunEnvAssocs
dun-env-assocs = ((3 ∷ 4 ∷ [] , short-beak ∷ short-beak ∷ []) , (1 , mildly-disturbed)) ∷
                 (([ 1 ] , [ short-beak ]) , (2 , undisturbed)) ∷
                 (([ 2 ] , [ long-beak ]) , (3 , mildly-disturbed)) ∷
                 (([ 5 ] , [ long-beak ]) , (4 , well-disturbed)) ∷
                 []

{- (I wish Agda had a normal list and vector syntax.  I don't care if the number
of characters is the same as Haskell/OCaml/Idris/Lean. It's still harder to read.) -}


-- The first element of each top level pairs in these lists is just there
-- to allow different types to live in the same list.  When processing
-- the envs or dunlins, it can be ignored (but might need to be recreated to
-- make the next set of envs and dunlins.
all-envs = assocs-to-envs dun-env-assocs
all-duns = assocs-to-duns dun-env-assocs

-----------------
-- Fitness and niche construction
-- IN PROGRESS

-- See docs/DunlinStory1.md for a sketch of possible rules to
-- use to implement `Dstep and `Estep in Niche.agda.

-- number of offspring for next generation
Fitness : Set
Fitness = ℕ

-- See docs/DunlinStory1.md for rationale, constraints
fitness : Dun → Env → Fitness
fitness (short-beak _ _) (undisturbed _ _)      = 0
fitness (short-beak _ _) (mildly-disturbed _ _) = 1
fitness (short-beak _ _) (well-disturbed _ _)   = 2
fitness (long-beak _ _)  (undisturbed _ _)      = 2
fitness (long-beak _ _)  (mildly-disturbed _ _) = 1
fitness (long-beak _ _)  (well-disturbed _ _)   = 0


lookup-env-by-loc : List Env → (loc : ℕ) → Maybe Env
lookup-env-by-loc [] _ = nothing
lookup-env-by-loc (env ∷ envs) loc = if loc == (env-loc env)
                                     then just env
                                     else lookup-env-by-loc envs loc

-- Should new envs be introduced here?  Maybe better to put in a separate step.
-- choose-kid-loc is some function from each dunlin to a new location. This can take
-- account the dunlin's current location, the dunlin's id, or other internal state
-- of the dunlin.  (This should be in field built into the Dun datatype instead, OO-style?)
reproduce : (max-id : ℕ) → (num-kids : ℕ) → (choose-kid-loc : Dun  → ℕ) → (parent : Dun) → List Dun
reproduce _ 0 _ _ = []
reproduce max-id (suc n) choose-loc (short-beak _ loc) = iterate next-dun (short-beak (suc max-id) loc) (suc n)
reproduce max-id (suc n) choose-loc (long-beak _ loc)  = iterate next-dun (long-beak  (suc max-id) loc) (suc n)
-- CHECK: Is max-id is getting incremented properly?

-- Calculates number of kids from fitness of dun relative to env, and calls reproduce.
-- Probably SHOULD BE MAYBE-IZED.  At present it returns an empty list when an env
-- can't be found.  This can't be distinguished from the zero fitness case.
reproduce-per-fit : (max-id : ℕ) → (envs : List Env) → (choose-loc : Dun → ℕ) →
                    (parent : Dun) → List Dun
reproduce-per-fit _ [] _ _ = []  -- No envs, shouldn't happen.
reproduce-per-fit max-id envs choose-loc parent with dun-loc parent
...                                                | loc with lookup-env-by-loc envs loc
...                                                         | nothing = [] -- can't find that env, shouldn't happen
...                                                         | just env = let fit = fitness parent env
                                                                         in if fit == 0
                                                                            then []
                                                                            else reproduce max-id fit choose-loc parent
-- (Lines are too long. Not sure what my indentation options are here.)


-- This location-chooser puts offspring in the same env as parent:
baby-loc-same : Dun → ℕ
baby-loc-same (short-beak id loc) = loc
baby-loc-same (long-beak id loc) =  loc

{-
add-duns-by-loc : (dloc : ℕ) → (offspring : List Dun) → (envs : List Env) → List Env
add-duns-by-loc _ _ [] = [] -- shouldn't occur: excluded by call from add-duns
add-duns-by-loc dloc offspring (env ∷ envs) = let (eloc , eduns) = env-params env
                                                  env-constr = env-constructor env
                                              in if dloc == eloc
                                                 then env-constr eloc (offspring ++ eduns) ∷ envs
                                                 else env ∷ (add-duns-by-loc dloc offspring envs)
-}

-- Assumes that env locations are unique.  (Maybe should be proven elsewhere?)
-- Inefficient.  Maybe new dunlins should be sorted by loc.
-- Or create a lookup structure.
add-dun : Dun → List Env → List Env
add-dun dun [] = [] -- no envs!
add-dun dun (env ∷ envs) = let env-loc = env-loc env
                               dunlins = env-duns env
                               env-constr = env-constructor env
                           in if (dun-loc dun) == env-loc
                              then (env-constr env-loc (dun ∷ env-duns)) ∷ envs
                              else env ∷ (add-dun dun envs)
                                                 
-- Must be a better way than this ...
add-duns : List Dun → List Env → List Env
add-duns [] envs = envs
add-duns (dun ∷ duns) envs = add-dun dun (add-duns duns envs)

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
--
-- TODO: -- Add removal of dead dunlins based on some criterion.
d-evolve : (max-id : ℕ) → List Env → (choose-loc : Dun → ℕ) → List Env
d-evolve max-id [] _ = []
d-evolve max-id envs choose-loc =
    let old-dunlins = L.concatMap env-duns envs
        new-dunlins = L.concatMap (reproduce-per-fit max-id envs choose-loc) old-dunlins -- make baby dunlins
        new-max-id = max-id + (L.length new-dunlins) -- should be a better way
    in add-duns new-dunlins envs

{-
-- THIS WORKS (or type checks) but seems unnecessarily complicated
d-evolve : (max-id : ℕ) → List Env → (choose-loc : Dun → ℕ) → List Env
d-evolve max-id [] _ = []
d-evolve max-id (env ∷ envs) choose-loc =
    let (loc , dunlins) = env-params env  -- get dunlins in next env
        new-dunlins = L.concatMap (reproduce-per-fit max-id env choose-loc) dunlins -- baby dunlins
    in add-duns new-dunlins                                 -- Add babies to envs
                (d-evolve (max-id + (L.length new-dunlins)) --  that result from adding other babies
                          envs choose-loc)                  --  to envs.
-}

niche-construct : Env → Env
niche-construct env = {!!}  -- extract dunlins, look up their effect, and construct new env

-- This modifies environments due to niche construction.  Since the dunlins that
-- perform the niche construction are referenced in the envs, we don't need to
-- pass them in separately.
e-evolve : List Env → List Env
e-evolve [] = []
e-evolve (env ∷ envs) = (niche-construct env) ∷ e-evolve envs
-}

-----------------------------------------------------------------------------
-- Experiments with mapping from locs to envs.  See CatMap.agda, 
-- https://agda.github.io/agda-stdlib/v2.0/README.Data.Tree.AVL.html

empty-env-map : EnvMap
empty-env-map = empty

singleton-env-map : EnvMap
singleton-env-map = singleton 1 (undisturbed [] 1)
-- size singleton-env-map
just-env1 = lookup singleton-env-map 1
nada = lookup singleton-env-map 42

-- Overwrites old element 1:
doubleton-env-map : EnvMap
doubleton-env-map = insert 2 (mildly-disturbed [] 2) singleton-env-map
just-env1again = lookup doubleton-env-map 1
just-env2 = lookup doubleton-env-map 2
nada-again = lookup doubleton-env-map 42
double-size = size doubleton-env-map

smaller-map : EnvMap
smaller-map = delete 1 doubleton-env-map
