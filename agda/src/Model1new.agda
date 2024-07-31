module Model1new where
-- First attempt at a relatively simple framework for natural selection with
-- niche construction.

{-

General notes on code below:

See docs/DunlinStory1.md for rationale for names, data, etc.

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

Since now each env contains a list of dunlins in it, an option might be
to iterate through the env list, and ignore the dunlin list.
However, it's still useful to separate niche construction, i.e.
modification of the (non-dunlins) state of environments from
updating dunlins.

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
-- note subst is actually from Relation.Binary.PropositionalEquality.Core

open import Niche
-- open import Kludges

--==========================================================--
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

-- Environments have locations that determine which environments
-- are adjacent.  Currently locations are nats, implying that each
-- environment is adjacent to no more than two others (perhaps along
-- the shoreline).  An alternative is to allow pairs of nats or integers
-- to represent environments arrayed in 2D space, or triples for 3D
-- coordinates, e.g. for fish in a body of water.
Loc : Set
Loc = ℕ

-- Dunlins have IDs as well as locations:
DunID : Set
DunID = ℕ


--==========================================================--
-- Dunlins

-- Each dunlin should have a unique id, and a location loc, which is an id
-- for the dunlin's current environment.  (It could be the env itself, but
-- I couldn't figure out how to do this kind of mutual recursion.)
data Dun : Loc → Set where
  short-beak   : (id : DunID) → (loc : Loc) → Dun loc
  long-beak  : (id : DunID) → (loc : Loc) → Dun loc

-- Abbreviation for the type of the Dun constructors will be useful later.
DunConstr : Set 
DunConstr = (id : DunID) → (loc : Loc) → Dun loc

-- Dunlins should be assigned unique ids.  This is the first one.
init-max-id : DunID
init-max-id = 0

-- Make a new dunlin using the provided constructor, creating a new id by
-- incrementing the previous max id that should be passed in.  The new id
-- can be extracted from the new dunlin as the new max id. -}
new-dun : DunConstr → (max-id : DunID) → (loc : Loc) → Dun loc
new-dun constr max-id loc = constr (suc max-id) loc

-- a list of dunlines at a location contains only dunlins with that location parameter
new-duns-at-loc : (max-id : DunID) → (loc : Loc) → List DunConstr → List (Dun loc)
new-duns-at-loc _ _ [] = []
new-duns-at-loc max-id loc (constr ∷ constrs) =
  let new-id = suc max-id
  in (constr new-id loc) ∷ (new-duns-at-loc new-id loc constrs)

-- For use inside List.iterate and similar functions to generate a
-- sequence of dunlins with consecutive ids.
next-dun : {loc₁ loc₂ : Loc} → Dun loc₁ → Dun loc₂
next-dun {loc₂ = loc₂} (short-beak id loc₁) = short-beak (suc id) loc₂
next-dun {loc₂ = loc₂} (long-beak id loc₁) = long-beak (suc id) loc₂

replace-dun-loc : {loc : Loc} → (dun : Dun loc) → (new-loc : Loc) → Dun new-loc
replace-dun-loc (short-beak id loc) new-loc = short-beak id new-loc
replace-dun-loc (long-beak id loc) new-loc = long-beak id new-loc

-- projection operators
dun-params : {loc : Loc} → Dun loc → (DunID × Loc)
dun-params (short-beak id loc) = (id , loc)
dun-params (long-beak id loc) = (id , loc)

dun-id : {loc : Loc} → Dun loc → DunID
dun-id (short-beak id _) = id 
dun-id (long-beak id _) = id

dun-loc : {loc : Loc} → Dun loc → Loc
dun-loc (short-beak _ loc) = loc 
dun-loc (long-beak _ loc) = loc

-- Is this non-idiomatic?
dun-constructor : {loc : Loc} → Dun loc → DunConstr
dun-constructor (short-beak _ _) = short-beak
dun-constructor (long-beak _ _) = long-beak

----------------
-- Experiment

-- Attempt to create lists of dunlins that are required to have the same location:
{-
data LocList (loc : Loc) : Set where
  ll-empty :  LocList loc
  ll-list : {constr : DunConstr} {id : DunID} → Dun → LocList loc
-}
-- This type checks but doesn't seem to capture what I want.
-- Maybe Dun to be indexed by Loc?

----------------

--=========================================================--
-- Environments

-- Environments have a location, loc, which is a unique id and also specifies
-- which environments are adjacent (e.g. env 5 is next to envs 4 and 6).
-- Environments also contain zero or more dunlins (i.e. Dun instances, rather
-- than mere dunlin ids).

{- In a future version, perhaps the level of disturbed-ness
should captured by a loc parameter rather than different
constructors.  If it's an index, that captures the idea that it's
a different type, and it might require using lists or vectors
over sigma pairs (Σ ℕ (Env ℕ)) instead of Envs.  (See
learning/Model1indexedID.agda in commit #3f46335 for
illustrations.) Perhaps the location id should be a type index as
well. -}

data Env : Loc → Set where  ---? are the implict and explicit locs the same? I want them to be.
  undisturbed      : {loc : Loc} → (duns : List (Dun loc)) → (loc : Loc) → Env loc
  mildly-disturbed : {loc : Loc} → (duns : List (Dun loc)) → (loc : Loc) → Env loc
  well-disturbed   : {loc : Loc} → (duns : List (Dun loc)) → (loc : Loc) → Env loc

-- Abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = {loc : Loc} → (duns : List (Dun loc)) → (loc : Loc) → Env loc

---------------------------------
---------------------------------
-- Experiment

{-
data EnvList (loc : Loc) : Set where
  ll-nil : EnvList loc
  ll-cons : (env : Env loc) (ls : EnvList loc) → EnvList loc

noenv : EnvList 42
noenv = ll-nil

oneenv : EnvList 42
oneenv = ll-cons (undisturbed [ (long-beak 6 47) ] 42) noenv

twoenvs : EnvList 42
twoenvs = ll-cons (mildly-disturbed [ (short-beak 5 47) ] 42) oneenv

-- This should fail, and it does:
threeenvs? : EnvList 42
threeenvs? = ll-cons (mildly-disturbed [ (short-beak 7 48) ] 44) twoenvs
-}

---------------------------------
---------------------------------

-- projection operators
env-loc : {loc : Loc} → Env loc → Loc
env-loc (undisturbed _ loc) = loc
env-loc (mildly-disturbed _ loc) = loc
env-loc (well-disturbed _ loc) = loc

{-
env-duns : {loc : Loc} {dunsa : List (Dun loc)} →  -- do I need these implicits?
           Env loc → List (Dun loc)
env-duns {loc} {duns} (undisturbed duns _) = duns -- how do I do this?
env-duns (mildly-disturbed duns _) = duns
env-duns (well-disturbed duns _) = duns
-}


-- Is this non-idiomatic?
env-constructor : {loc : Loc} → Env loc → EnvConstr
env-constructor (undisturbed _ _) = undisturbed
env-constructor (mildly-disturbed _ _) = mildly-disturbed
env-constructor (well-disturbed _ _) = well-disturbed


--==========================================================--
-- EnvMap: A map structure that stores envs, allows lookup by
-- location, and enforces unique locations within the structure.
-- (Duns in an Env can be found because the `duns` argument contains
-- all dunlins in the environment.  In order to find a dunlin's
-- environment from a Dun, we use the `loc` argument to perform
-- a lookup on the EnvMap for the system.)

-- This works because Env is indexed by loc.
EnvMap = Tree (MkValue Env (subst Env))

-- I still don't understand what's going on in MkValue, but it appears
-- that the first arg and the arg to subst should be an indexed datatype
-- (or a function?) where indexes are keys. i.e. this provides a map
-- from keys to values in which the keys are indexes of the value type.
-- (Data.Tree.AVL.IndexedMap provides a way to do somethng similar,
-- but I don't understand how to use it. To allow values to be
-- independent of keys use Data.Tree.AVL.Map.)

-- It seems convenient to use a list in a special format to initialize
-- a model, using config-system below.
-- See Model Parameters section for an illustration.
ConfigInfo : Set
ConfigInfo = List (ℕ × EnvConstr × List DunConstr)

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


--==========================================================--
-- Tools for modifying dunlin-environment relationships

--------------------
-- Remove a dunlin:

-- Silently returns the same list of dunlins is the dun argument
-- doesn't apepar in the list. (Add proof?)
remove-dun-from-list : {loc : Loc} → (dun : Dun loc) → (duns : List (Dun loc)) → List (Dun loc)
remove-dun-from-list dun [] = []
remove-dun-from-list dun (x ∷ duns) = if (dun-id dun) == (dun-id x)
                                      then duns
                                      else remove-dun-from-list dun duns

-- Has the same silent failure behavior as remove-dun-from-list.
---? I do not understand what I've done below with duns₂ ; it's what Agda
---? guided me to, and seems to work.
remove-dun-from-env : {loc : Loc} → {duns : List (Dun loc)} →
                      (dun : (Dun loc)) → (env : Env loc) → Env loc
remove-dun-from-env {duns = duns₂} dun (undisturbed duns loc) =
   undisturbed (remove-dun-from-list dun duns₂) loc
remove-dun-from-env {duns = duns₂} dun (mildly-disturbed duns loc) =
   mildly-disturbed (remove-dun-from-list dun duns₂) loc
remove-dun-from-env {duns = duns₂} dun (well-disturbed duns loc) =
   well-disturbed (remove-dun-from-list dun duns₂) loc

-- Silently returns the same EnvMap if there's a misconfiguration
-- such that the dunlin's location doesn't appear in envs. (Add proof?)
remove-dun-from-envs : {loc : Loc} → (dun : Dun loc) → (envs : EnvMap) → EnvMap
remove-dun-from-envs dun envs = let loc = dun-loc dun
                                in case (lookup envs loc) of λ where 
                                  nothing → envs
                                  (just env) →
                                    insert loc (remove-dun-from-env {!!} env) envs -- overwrites old value

--------------------
-- Add a dunlin:

add-dun-to-env : {loc : Loc} → (dun : Dun loc) → (env : Env loc) → Env loc
add-dun-to-env dun (undisturbed duns loc) = undisturbed (dun ∷ {!!}) loc
add-dun-to-env dun (mildly-disturbed duns loc) = mildly-disturbed (dun ∷ {!!}) loc
add-dun-to-env dun (well-disturbed duns loc) = well-disturbed (dun ∷ {!!}) loc

add-dun-to-envs : {loc : Loc} → (dun : Dun loc) → (envs : EnvMap) → EnvMap
add-dun-to-envs dun envs = let loc = dun-loc dun
                           in case (lookup envs loc) of λ where
                             nothing → envs
                             (just env) → insert loc (add-dun-to-env {!!} env) envs -- overwrites old value

-- Does unnecessary work when multiple dunlins are added to the same environment;
-- they could all be added at once instead of calling add-dun repeatedly.
add-duns-to-envs : {loc : Loc} → List (Dun loc) → EnvMap → EnvMap
add-duns-to-envs [] envs = envs
add-duns-to-envs (dun ∷ duns) envs = add-dun-to-envs dun (add-duns-to-envs duns envs)

--------------------
-- Dunlin movement between environments

-- Note this doesn't restrict movement to adjacent environments.  That has
-- to be imposed elsewhere. (It's not necessarily required for birds, anyway.)
move-to-env : {loc : Loc} → (dun : Dun loc) → (new-loc : Loc) → (envs : EnvMap) → EnvMap
move-to-env dun new-loc envs = add-dun-to-envs (replace-dun-loc dun new-loc)
                                               (remove-dun-from-envs dun envs)

-- TODO: Add move-north (increment location) and move-south (decrement location)
-- functions?

-- QUESTION: What should the policy when dunlin tries to move past the
-- minimum or maximum environment?
-- a. Leave dunlin in same environment
-- b. Make a "toroidal"/"periodic boundary conditions" world, i.e. circular in 1D.
--    i.e. going beyond the minimum environment places one in the max env, etc.
-- c. Make it an error, i.e. "Maybe-ize" movement.

--------------------
-- General-purpose

{- Not possible with indexed dunlins.  Probably should use an AVL tree.

-- Generate a list of all dunlins in all environments.
-- Tip: toList produces a list of AVL.Value.K& pairs, not Σ-pairs, and
-- commas in the result of toList are for Data.Tree.AVL.Value.K&, not Σ .
collect-all-duns : EnvMap → List Dun
collect-all-duns envs = concatMap (env-duns ∘ Value.K&_.value) $ toList envs

-}

--==========================================================--
-- Fitness, reproduction, movement, and death.  

-- See docs/DunlinStory1.md for a sketch of possible rules to
-- use to implement `Dstep and `Estep in Niche.agda.

--------------------
-- Fitness

-- number of offspring for next generation
Fitness : Set
Fitness = ℕ

FitnessFn : Set
FitnessFn = {loc : Loc} → Dun loc → Env loc → Fitness

--------------------
-- Reproduction

-- Should new envs be introduced here?  Maybe better to put in a separate step.
-- choose-child-loc is some function from each dunlin to a new location. This can take
-- account the dunlin's current location, the dunlin's id, or other internal state
-- of the dunlin.  (This should be in field built into the Dun datatype instead, OO-style?)
-- THE RETURN VALUE SHOULD NOT BE REQUIRED TO BE DUNLINS ALL IN THE SAME LOCATION.
-- SO RETURN A LIST OF SIGMA PAIRS OR AN AVL TREE, OR ?
reproduce : {loc : Loc} → (max-id : ℕ) → (num-childs : ℕ) →
            (choose-child-loc : (Dun loc) → ℕ) → (parent : Dun loc) → List (Dun loc)
reproduce _ 0 _ _ = []
reproduce max-id (suc n) choose-loc (short-beak _ loc) =
   iterate next-dun (short-beak (suc max-id) loc) (suc n)
reproduce max-id (suc n) choose-loc (long-beak _ loc) =
   iterate next-dun (long-beak  (suc max-id) loc) (suc n)
-- CHECK: Is max-id is getting incremented properly?

-- Calculates number of childs from fitness of dun relative to env, and calls reproduce.
-- Probably SHOULD BE MAYBE-IZED.  At present it returns an empty list when an env
-- can't be found.  This can't be distinguished from the zero fitness case.
-- THE RETURN VALUE SHOULD NOT BE REQUIRED TO BE DUNLINS ALL IN THE SAME LOCATION.
-- SO RETURN A LIST OF SIGMA PAIRS OR AN AVL TREE, OR ?
reproduce-per-fit : {loc : Loc} → (max-id : ℕ) → (envs : EnvMap) → (fitfn : FitnessFn) →
                    (choose-loc : (Dun loc) → ℕ) → (parent : Dun loc) → List (Dun loc)  -- parent is last to use currying
reproduce-per-fit max-id envs fitfn choose-loc parent
                  with dun-loc parent
...               | loc with lookup envs loc
...                     | nothing = [] -- can't find that env, shouldn't happen
...                     | just env = let fit = fitfn parent {!!} -- env
                                     in if fit == 0
                                        then []
                                        else reproduce max-id fit choose-loc parent

--------------------
-- Movement of dunlins from one environment to another

-- TODO

--------------------
-- Death

-- TODO: -- Add removal of dead dunlins based on some criterion.


--==========================================================--
-- Niche construction, i.e. modification of environments due to
-- dunlins in them.

-- TODO

--==========================================================--
-- Top-level evolution functions

-- Since this model stores dunlins inside environments, we can update the dunlins
-- by iterating through the envs.  There are several things that might need to happen:
--   Determine each dunlin's fitness
--   Create new dunlins as a response, and place them in some environments.
--   Change state of environments in response to niche construction by dunlins.
--   Possibly change state of environments in response to states of neighboring envs.
--   Allow old dunlins to move to adjacent environments.
-- These need not all be done by d-evolve.  Callan's idea of modifying
-- dunlins and envs separately is a good idea.
-- max-dun-id is the previous maximum dunlin-id, which should be passed to new-dunlin,
-- which will increment it.

-- Not sure whether the env change should be in a separate e-evolve function.

-- choose-loc is a function such as child-loc-same that determines the new
-- location of offspring of a parent dunlin.  (In a future version, this
-- might be a set of locations or a probability distribution over locations.)

{-
d-evolve : (max-id : ℕ) → EnvMap → (fitfn : FitnessFn) → (choose-loc : Dun → ℕ) → (ℕ × EnvMap)
d-evolve max-id envs fitfn choose-loc =
  let old-dunlins = collect-all-duns envs  -- need to revise for indexed dunlins
      new-dunlins = L.concatMap (reproduce-per-fit max-id envs fitfn choose-loc) old-dunlins -- make baby dunlins
      new-max-id = max-id + (L.length new-dunlins) -- Is there be a better way?
  in (new-max-id , add-duns-to-envs new-dunlins envs)
-}


--==========================================================--
-- Model Parameters
-- Initial configuration of an example system.
-- This should ultimately be moved to another file, or replaced there.

------------------------
-- Initial configuration of environments and dunlins.
-- They should be constructed together so that location
-- relationships will be consistent.

config-info : ConfigInfo
config-info =
  (1 , mildly-disturbed , (short-beak ∷ short-beak ∷ [])) ∷
  (2 , undisturbed , (short-beak ∷ [])) ∷ 
  (3 , mildly-disturbed , (long-beak ∷ [])) ∷
  (4 , well-disturbed , (long-beak ∷ [])) ∷
  []

all-envs : EnvMap
all-envs = config-system init-max-id config-info empty

{- Informal testing (convert to equality proofs?):

maybe-env : Maybe (Env 1)
maybe-env = lookup all-envs 1
all-envs-list = toList all-envs

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

--------------------
-- Fitness rules--these determine how many offspring a dunlin has in a given
-- environment. See docs/DunlinStory1.md for rationale, constraints
fitness : {loc : Loc} → Dun  loc → Env loc → Fitness
fitness (short-beak _ _) (undisturbed _ _)      = 0
fitness (short-beak _ _) (mildly-disturbed _ _) = 1
fitness (short-beak _ _) (well-disturbed _ _)   = 2
fitness (long-beak _ _)  (undisturbed _ _)      = 2
fitness (long-beak _ _)  (mildly-disturbed _ _) = 1
fitness (long-beak _ _)  (well-disturbed _ _)   = 0

-- This location-chooser puts offspring in the same env as parent:
child-loc-same : {loc : Loc} → Dun  loc → ℕ
child-loc-same (short-beak id loc) = loc
child-loc-same (long-beak id loc) =  loc

-------------------
-- Death rules

-- TO ADD

--------------------
-- Niche construction rules

-- TO ADD 
