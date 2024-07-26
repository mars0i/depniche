module Model1 where

-- See docs/DunlinStory1.md for rationale for names, data, etc.

{- General notes on code

After looking at the Example module in Niche.agda, I wanted to do
something slightly more involved  with the dunlin and environment
types in order to implement the transition rules Dstep and Estep.
I wasn't sure how to fill in the holes left in the e-evolve
function; I needed a story to motivate the rules, and that meant
changing the dunlin and environment types.

I'm not sure if the way I did this is a good idea, and it doesn't
quite fit what I'd originally envisioned (which may be a bad idea
anyway).  I just wanted to get something working, and it was a
learning experience, but I may have gone down a bad path, or I
might have made poor choices within a good path. So I have no
problem with this being revised or completely rethought and
rewritten from scratch.

The original example in Niche.agda also had a timestep parameter, but 
the transition rules can be the same at every time.
Since each env contains a list of dunlins in it, an option might be
to iterate through the env list, and ignore the dunlin list.

Another change is that updating the system now passs along a maximum
dunlin id, so that each new dunlin can get a unique id that can be used
to track the identity over time of functionally updated dunlins.

-}

open import Function.Base using (_∘_; _$_; case_of_; case_returning_of_)
open import Agda.Builtin.Nat using (_==_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_)
open import Data.Nat.Properties using (<-strictTotalOrder) -- for AVL modules
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; _,′_) -- Needs stdlib 2.0
open import Data.Bool using (if_then_else_) -- add case_of_ , etc?
open import Data.List as L using (List; _∷_; []; [_]; iterate; _++_; map; concat; concatMap; zipWith; _[_]%=_; _[_]∷=_)
-- open import Data.Vec as V using (Vec; _∷_; [])

import Data.Tree.AVL as AVL using (Tree; MkValue; empty; singleton; insert; insertWith; delete; lookup; map; size; toList; toPair) -- K&_; 
import Data.Tree.AVL.Value as Value ---? I don't know how to import K&.value separately
open AVL <-strictTotalOrder
open import Relation.Binary.PropositionalEquality using (subst) -- _≡_; refl

open import Niche
-- open import Kludges

----------------------------------------------------------
-- Dun and Env types
-- These correspond to the D and E defs in Niche.Example.
-- See docs/DunlinStory1.md for rationale for names, data, etc.

{- Overview of choices made:
 
Duns in an environment can be found from the Env they're in
because those Duns will be stored in a List (or Vec) in the Env. 
(There may be ways to store the Envs in the Duns as well, but the
obvious ways lead to nontermination, and I don't think it's the
trouble.)

There is a fixed number of locations, while dunlins are born and
die.

Dunlins have ids, but these are not indexes, to make it easier to
store Duns in a List in an Env.  The ids aren't needed to evolve
the population, but they're likely to be useful for tracking a
dunlin over time as it changes state (i.e. as it is replaced by a
new Dun with the same id).

Env ids are locations, and they are indexes.  This makes it esy
all Envs in a map in the form of an AVL tree, allowing lookup by
location from a Dun, and forcing envs at locations to be unique.

Dun ids should be unique as well--maybe it would be better to
provide a a lookup map for dunlins too--but only to allow tracking
of the states of a dunlin over time.  This can be useful, even
though it's not relevant to evolution in a population.

-}

-----------------------------------

-- Environments have locations that determine which environments
-- are adjacent.  Currently locations are nats, implying that each
-- environment is adjacent to no more than two others (perhaps along
-- the shoreline).  An alternative is to allow pairs of nats or integers
-- to represent environments arrayed in 2D space, or triples for 3D
-- coordinates, e.g. for fish in a body of water.
Loc : Set
Loc = ℕ

-- Dunlins have IDs:
DunID : Set
DunID = ℕ


-----------------------------------
-- Dunlins

-- Each dunlin should have a unique id, and a location loc, which is an id
-- for the dunlin's current environment.  (It could be the env itself, but
-- I couldn't figure out how to do this kind of mutual recursion.)
data Dun : Set where
  short-beak   : (id : DunID) → (loc : Loc) → Dun
  long-beak  : (id : DunID) → (loc : Loc) → Dun

-- An abbreviation for the type of the Dun constructors will be useful later.
DunConstr : Set 
DunConstr = (id : DunID) → (loc : Loc) → Dun

init-max-id : DunID
init-max-id = 1

-- Make a new dunlin using the provided constructor, creating a new id by
-- incrementing the previous max id that should be passed in.  The new id
-- can be extracted from the new dunlin as the new max id.
new-dun : DunConstr → (max-id : DunID) → (loc : Loc) → Dun
new-dun constr max-id loc = constr (suc max-id) loc

new-duns-at-loc : (max-id : DunID) → (loc : Loc) → List DunConstr → List Dun
new-duns-at-loc _ _ [] = []
new-duns-at-loc max-id loc (constr ∷ constrs) =
  let new-id = suc max-id
  in (constr new-id loc) ∷ (new-duns-at-loc new-id loc constrs)

-- For use inside List.iterate and similar functions to generate a
-- sequence of dunlins with consecutive ids.
next-dun : Dun → Dun
next-dun (short-beak id loc) = short-beak (suc id) loc
next-dun (long-beak id loc) = long-beak (suc id) loc

{-
move-north : Dun → Dun
move-north (short-beak id loc) = short-beak id (1 + loc)
move-north (long-beak id loc) = long-beak id (1 + loc)

move-south : Dun → Dun
move-south (short-beak id loc) = short-beak id (loc - 1)
move-south (long-beak id loc) = long-beak id (loc - 1)
-}

-- projection operators
dun-params : Dun → (DunID × Loc)
dun-params (short-beak id loc) = (id , loc)
dun-params (long-beak id loc) = (id , loc)

dun-id : Dun → DunID
dun-id (short-beak id _) = id 
dun-id (long-beak id _) = id

dun-loc : Dun → Loc
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
data Env : Loc → Set where
  undisturbed      : (dunlins : List Dun) → (loc : Loc) → Env loc
  mildly-disturbed : (dunlins : List Dun) → (loc : Loc) → Env loc
  well-disturbed   : (dunlins : List Dun) → (loc : Loc) → Env loc
-- In a future version, perhaps the level of disturbed-ness should captured by an loc
-- parameter rather than different constructors.  If it's an index, that captures
-- the idea that it's a different type, and it might require using lists or
-- vectors over sigma pairs (Σ ℕ (Env ℕ)) instead of Envs.  (See
-- learning/Model1indexedID.agda in commit #3f46335 for illustrations.)
-- Perhaps the location id should be a type index as well.

-- An abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = (duns : List Dun) → (loc : Loc) → Env loc

env-loc : {loc : Loc} → Env loc → Loc
env-loc (undisturbed _ loc) = loc
env-loc (mildly-disturbed _ loc) = loc
env-loc (well-disturbed _ loc) = loc

env-duns : {loc : Loc} → Env loc → List Dun
env-duns (undisturbed dunlins _) = dunlins
env-duns (mildly-disturbed dunlins _) = dunlins
env-duns (well-disturbed dunlins _) = dunlins

-- Is this non-idiomatic?
env-constructor : {loc : Loc} → Env loc → EnvConstr
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

ConfigInfo : Set
ConfigInfo = List (ℕ × EnvConstr × List DunConstr)

config-info : ConfigInfo
config-info =
  (1 , mildly-disturbed , (short-beak ∷ short-beak ∷ [])) ∷
  (2 , undisturbed , (short-beak ∷ [])) ∷ 
  (3 , mildly-disturbed , (long-beak ∷ [])) ∷
  (4 , well-disturbed , (long-beak ∷ [])) ∷
  []

-- This is doing roughly what mkSys does in Niche.agda, and they
-- should probably be harmonized and merged, or this could provide
-- a component of mkSys.
config-system : (max-id : ℕ) → ConfigInfo → EnvMap → EnvMap
config-system _ [] env-map = env-map
config-system max-id (env-spec ∷ env-specs) env-map =
  let (loc , env-constr , dun-constrs) = env-spec
      duns = new-duns-at-loc init-max-id loc dun-constrs
      new-max-id = max-id + L.length duns
      new-env = env-constr duns loc
  in config-system new-max-id env-specs (insert loc new-env env-map)

all-envs : EnvMap
all-envs = config-system init-max-id config-info empty

-- Checks (convert to equality proofs?):
maybe-env : Maybe (Env 1)
maybe-env = lookup all-envs 1
all-envs-list = toList all-envs
{-
all-envs-list should be:

    (1 Data.Tree.AVL.Value.,
     mildly-disturbed (short-beak 2 1 ∷ short-beak 3 1 ∷ []) 1)
    ∷
    (2 Data.Tree.AVL.Value., undisturbed (short-beak 2 2 ∷ []) 2) ∷
    (3 Data.Tree.AVL.Value., mildly-disturbed (long-beak 2 3 ∷ []) 3) ∷
    (4 Data.Tree.AVL.Value., well-disturbed (long-beak 2 4 ∷ []) 4) ∷
    []

Note that "Data.Tree.AVL.Value." qualifies ",".  i.e. this is the comma
from Data.Tree.AVL.Value (via Data.Tree.AVL.Indexed), which is *not* the
Σ-pair constructor; it's the K& constructor.  (There are however functions
toPair and fromPair in AVL.Value that convert to/from the Σ-pair.)

-}


-----------------------------
-- Modifying dunlin-environment relationships

remove-dun-from-list : (dun : Dun) → (duns : List Dun) → List Dun
remove-dun-from-list dun [] = []
remove-dun-from-list dun (x ∷ duns) = if (dun-id dun) == (dun-id x)
                                      then duns
                                      else remove-dun-from-list dun duns

remove-dun-from-env : {loc : Loc} → (dun : Dun) → (env : Env loc) → Env loc
remove-dun-from-env dun (undisturbed duns loc) =
   undisturbed (remove-dun-from-list dun duns) loc
remove-dun-from-env dun (mildly-disturbed duns loc) =
   mildly-disturbed (remove-dun-from-list dun duns) loc
remove-dun-from-env dun (well-disturbed duns loc) =
   well-disturbed (remove-dun-from-list dun duns) loc

-- Trying to use AVL.insertWith
-- Needs to produce function from maybe to env for use in insertWith.
-- How is this supposed to work?  What do do with nothing??
remove-dun-from-maybe-env : {loc : Loc} → (dun : Dun) → (envs : EnvMap) → (maybe-env : Maybe (Env loc)) → Env loc
remove-dun-from-maybe-env dun envs (just env) = remove-dun-from-env dun env
remove-dun-from-maybe-env dun envs nothing = {!!}

remove-dun-from-envs : (dun : Dun) → (envs : EnvMap) → Maybe EnvMap
remove-dun-from-envs (short-beak id loc) envs = {!!}
remove-dun-from-envs (long-beak id loc) envs = {!!}

add-dun-to-envs : (dun : Dun) → (envs : EnvMap) → Maybe EnvMap
add-dun-to-envs dun envs = {!!}

move-to-env : (mover : Dun) → (new-loc : Loc) → (envs : EnvMap) → EnvMap
move-to-env (short-beak id loc) new-loc envs = {!!}
move-to-env (long-beak id loc) new-loc envs = {!!}


-----------------
-- Fitness and niche construction
-- IN PROGRESS

-- See docs/DunlinStory1.md for a sketch of possible rules to
-- use to implement `Dstep and `Estep in Niche.agda.

-- number of offspring for next generation
Fitness : Set
Fitness = ℕ

-- See docs/DunlinStory1.md for rationale, constraints
fitness : {loc : Loc} → Dun → Env loc → Fitness
fitness (short-beak _ _) (undisturbed _ _)      = 0
fitness (short-beak _ _) (mildly-disturbed _ _) = 1
fitness (short-beak _ _) (well-disturbed _ _)   = 2
fitness (long-beak _ _)  (undisturbed _ _)      = 2
fitness (long-beak _ _)  (mildly-disturbed _ _) = 1
fitness (long-beak _ _)  (well-disturbed _ _)   = 0

-- Should new envs be introduced here?  Maybe better to put in a separate step.
-- choose-kid-loc is some function from each dunlin to a new location. This can take
-- account the dunlin's current location, the dunlin's id, or other internal state
-- of the dunlin.  (This should be in field built into the Dun datatype instead, OO-style?)
reproduce : (max-id : ℕ) → (num-kids : ℕ) → (choose-kid-loc : Dun  → ℕ) → (parent : Dun) → List Dun
reproduce _ 0 _ _ = []
reproduce max-id (suc n) choose-loc (short-beak _ loc) =
   iterate next-dun (short-beak (suc max-id) loc) (suc n)
reproduce max-id (suc n) choose-loc (long-beak _ loc) =
   iterate next-dun (long-beak  (suc max-id) loc) (suc n)
-- CHECK: Is max-id is getting incremented properly?

-- Calculates number of kids from fitness of dun relative to env, and calls reproduce.
-- Probably SHOULD BE MAYBE-IZED.  At present it returns an empty list when an env
-- can't be found.  This can't be distinguished from the zero fitness case.
reproduce-per-fit : (max-id : ℕ) → (envs : EnvMap) → (choose-loc : Dun → ℕ) →
                    (parent : Dun) → List Dun
reproduce-per-fit max-id envs choose-loc parent with dun-loc parent
...                                                | loc with lookup envs loc
...                                                         | nothing = [] -- can't find that env, shouldn't happen
...                                                         | just env = let fit = fitness parent env
                                                                         in if fit == 0
                                                                            then []
                                                                            else reproduce max-id fit choose-loc parent
---? (Lines are too long. Not sure what indentation options are using `with`.)


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

-- Is there an easy way to remove the redundancy in the with-results?
add-dun : Dun → EnvMap → EnvMap
add-dun dun envs with lookup envs (dun-loc dun)
...              | just (undisturbed dunlins loc) = insert loc (undisturbed (dun ∷ dunlins) loc) envs
...              | just (mildly-disturbed dunlins loc) = insert loc (mildly-disturbed (dun ∷ dunlins) loc) envs
...              | just (well-disturbed dunlins loc) = insert loc (well-disturbed (dun ∷ dunlins) loc) envs
...              | nothing = envs

-- Does unnecessary work when multiple dunlins are added to the same environment;
-- they could all be added at once instead of calling add-dun repeatedly.
add-duns : List Dun → EnvMap → EnvMap
add-duns [] envs = envs
add-duns (dun ∷ duns) envs = add-dun dun (add-duns duns envs)

-- Should the result be a Vec or an AVL map instead of a list?
collect-all-duns : EnvMap → List Dun
collect-all-duns envs = concatMap (env-duns ∘ Value.K&_.value) $ toList envs
-- Tip: toList produces a list of AVL.Value.K& pairs, not Σ-pairs.
-- (Commas in the result of toList are for Data.Tree.AVL.Value.K&, not Σ .)

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

-- choose-loc is a function such as baby-loc-same that determines the new
-- location of offspring of a parent dunlin.  (In a future version, this
-- might be a set of locations or a probability distribution over locations.)
d-evolve : (max-id : ℕ) → EnvMap → (choose-loc : Dun → ℕ) → (ℕ × EnvMap)
d-evolve max-id envs choose-loc =
  let old-dunlins = collect-all-duns envs
      new-dunlins = L.concatMap (reproduce-per-fit max-id envs choose-loc) old-dunlins -- make baby dunlins
      new-max-id = max-id + (L.length new-dunlins) -- Is there be a better way?
  in (new-max-id , add-duns new-dunlins envs)

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


{-
FIXME:

niche-construct : Env → Env
niche-construct env = {!!}  -- extract dunlins, look up their effect, and construct new env

-- This modifies environments due to niche construction.  Since the dunlins that
-- perform the niche construction are referenced in the envs, we don't need to
-- pass them in separately.
e-evolve : List Env → List Env
e-evolve [] = []
e-evolve (env ∷ envs) = (niche-construct env) ∷ e-evolve envs

-}
