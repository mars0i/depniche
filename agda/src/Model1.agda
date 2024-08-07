-- Attempt at a relatively simple framework for natural selection with
-- niche construction.

module Model1 where

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

{- There are a number of verbose, repetitious function definitions below.
   They're written this way in order to expose parameters such as `loc`
   so as to allow Agda to see that all references to loc are the same.

   Surely this sort of code is not required by Agda, but I couldn't
   figure out a better way.
-}

open import Function.Base using (_∘_; _$_; case_of_; case_returning_of_)
open import Data.Bool using (if_then_else_) -- add case_of_ , etc?

-- open import Data.Integer as I using (ℤ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (<-strictTotalOrder) -- for AVL modules

open import Data.List as L using (List; _∷_; []; [_]; iterate; _++_; map; concat; concatMap; zipWith; _[_]%=_; _[_]∷=_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂; _,′_)

-- open import Data.Vec as V using (Vec; _∷_; [])
import Data.Tree.AVL as AVL using (Tree; MkValue; empty; singleton; insert; insertWith; delete; lookup; map; size; toList; fromList; toPair; const) -- K&_; 
import Data.Tree.AVL.Value as Value ---? I don't know how to import K&.value separately
open AVL <-strictTotalOrder -- Since the arg comes from Data.Nat.Properties, keys are ℕ's.
import Data.Tree.AVL.Map as Map using (Map; fromList)
open Map <-strictTotalOrder -- Since the arg comes from Data.Nat.Properties, keys are ℕ's.


open import Relation.Binary.PropositionalEquality using (subst; _≡_; refl)
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

-- e.g. for lists containing Duns
DunLocPair : Set
DunLocPair = Σ Loc Dun

dun-to-locpair : {loc : Loc} → Dun loc → DunLocPair
dun-to-locpair dun@(short-beak id loc) = loc , short-beak id loc
dun-to-locpair dun@(long-beak id loc) =  loc , long-beak id loc


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
dun-constr : {loc : Loc} → Dun loc → DunConstr
dun-constr (short-beak _ _) = short-beak
dun-constr (long-beak _ _) = long-beak



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

-- This enforce that the dunlins in the embedded list have the same
-- location as the environment (now that the loc arg comes first).
data Env : Loc → Set where
  undisturbed      : (loc : Loc) → (duns : List (Dun loc)) → Env loc
  mildly-disturbed : (loc : Loc) → (duns : List (Dun loc)) → Env loc
  well-disturbed   : (loc : Loc) → (duns : List (Dun loc)) → Env loc

-- Abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = (loc : Loc) → (duns : List (Dun loc)) → Env loc

-- e.g. for lists containing Envs
EnvLocPair : Set
EnvLocPair = Σ Loc Env

env-to-locpair : {loc : Loc} → Env loc → EnvLocPair
env-to-locpair (undisturbed loc duns) = loc , undisturbed loc duns
env-to-locpair (mildly-disturbed loc duns) = loc , mildly-disturbed loc duns
env-to-locpair (well-disturbed loc duns) = loc , well-disturbed loc duns

-- EnvMap: A map structure that stores envs, allows lookup by
-- location, and enforces unique locations within the structure.
-- (Duns in an Env can be found because the `duns` argument contains
-- all dunlins in the environment.  In order to find a dunlin's
-- environment from a Dun, we use the `loc` argument to perform
-- a lookup on the EnvMap for the system.)
-- This works because Env is indexed by loc.
EnvMap = Tree (MkValue Env (subst Env))

---------------------------------
---------------------------------

-- projection operators
env-loc : {loc : Loc} → Env loc → Loc
env-loc (undisturbed loc _) = loc
env-loc (mildly-disturbed loc _) = loc
env-loc (well-disturbed loc _) = loc

env-duns : {loc : Loc} → (Env loc) → List (Dun loc)
env-duns (undisturbed loc duns) = duns
env-duns (mildly-disturbed loc duns) = duns
env-duns (well-disturbed loc duns) = duns


-- Is this non-idiomatic?
env-constr : {loc : Loc} → Env loc → EnvConstr
env-constr (undisturbed _ _) = undisturbed
env-constr (mildly-disturbed _ _) = mildly-disturbed
env-constr (well-disturbed _ _) = well-disturbed


--==========================================================--

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
      new-env = env-constr loc duns
  in config-system new-max-id env-specs (insert loc new-env env-map)


--==========================================================--
-- Tools for modifying dunlin-environment relationships

--------------------
-- Remove a dunlin:

-- Silently returns the same list of dunlins is the dun argument
-- doesn't apepar in the list. (Add proof?)
remove-dun-from-list : {loc : Loc} → (dun : Dun loc) → (duns : List (Dun loc)) → List (Dun loc)
remove-dun-from-list dun [] = []
remove-dun-from-list dun (x ∷ duns) = if (dun-id dun) ≡ᵇ (dun-id x)   -- IS THIS A PROBLEM?
                                      then duns
                                      else remove-dun-from-list dun duns

{- About errors like this one:
      _duns_142 : List (Dun loc)  [ at /Users/marshall/docs/src/depniche/agda/src/Model1new.agda:324,97-116 ]
   Naïm Camille Favier says (https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Mysterious.20error.20message/near/455722851):
   "it's an unsolved metavariable. agda should highlight the source of the metavariable with a yellow background
   the name gives you a hint: it's probably an implicit argument named `duns` to some function call which agda couldn't infer"
-}

-- This works--got rid of funky metavariable errors--but surely there's some way to be less verbose.
remove-dun-from-envs : {loc : Loc} → (dun : Dun loc) → (envs : EnvMap) → EnvMap
remove-dun-from-envs dun@(short-beak id loc) envs
    with lookup envs loc
... | nothing = envs
... | just (undisturbed loc duns) =      insert loc (undisturbed loc (remove-dun-from-list dun duns)) envs
... | just (mildly-disturbed loc duns) = insert loc (mildly-disturbed loc (remove-dun-from-list dun duns)) envs
... | just (well-disturbed loc duns) =   insert loc (well-disturbed loc (remove-dun-from-list dun duns)) envs
remove-dun-from-envs dun@(long-beak id loc) envs
    with lookup envs loc
... | nothing = envs
... | just (undisturbed loc duns) =      insert loc (undisturbed loc (remove-dun-from-list dun duns)) envs
... | just (mildly-disturbed loc duns) = insert loc (mildly-disturbed loc (remove-dun-from-list dun duns)) envs
... | just (well-disturbed loc duns) =   insert loc (well-disturbed loc (remove-dun-from-list dun duns)) envs


--------------------
-- Add a dunlin:

---? I do not understand what I've done below with subscripted variables ;
---? it's what Agda guided me to, but it type checks.
-- DOES IT BEHAVE CORRECTLY?
add-dun-to-env : {loc : Loc} → {duns : List (Dun loc)} →
                 (dun : Dun loc) → (env : Env loc) → Env loc
add-dun-to-env {duns = duns₁} dun (undisturbed loc duns) =
   undisturbed loc (dun ∷ duns₁)
add-dun-to-env {duns = duns₁} dun (mildly-disturbed loc duns) =
   mildly-disturbed loc (dun ∷ duns₁)
add-dun-to-env {duns = duns₁} dun (well-disturbed loc duns) =
   well-disturbed loc (dun ∷ duns₁)

-- This works--got rid of funky metavariable errors--but surely there's some way to be less verbose.
add-dun-to-envs : {loc : Loc} → (dun : Dun loc) → (envs : EnvMap) → EnvMap
add-dun-to-envs dun@(short-beak id loc) envs
    with lookup envs loc
... | nothing = envs
... | just (undisturbed loc duns) =      insert loc (undisturbed loc (dun ∷ duns)) envs
... | just (mildly-disturbed loc duns) = insert loc (mildly-disturbed loc (dun ∷ duns)) envs
... | just (well-disturbed loc duns) =   insert loc (well-disturbed loc (dun ∷ duns)) envs
add-dun-to-envs dun@(long-beak id loc) envs
    with lookup envs loc
... | nothing = envs
... | just (undisturbed loc duns) =      insert loc (undisturbed loc (dun ∷ duns)) envs
... | just (mildly-disturbed loc duns) = insert loc (mildly-disturbed loc (dun ∷ duns)) envs
... | just (well-disturbed loc duns) =   insert loc (well-disturbed loc (dun ∷ duns)) envs

-- Add dunlins to a single environment.  The dunlins must all have the same loc index.
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
-- a. Leave dunlin in same environment.  This will result in unnatural clumping
-- near ends unless there are behaviors that counteract it.
-- b. Dunlins that try to go past the end "bounce" in the other direction.
-- b. Make a "toroidal"/"periodic boundary conditions" world, i.e. circular in 1D.
--    i.e. going beyond the minimum environment places one in the max env, etc.
--    Clearly unnatural, but it's a common way of simulating an infinite space.
-- c. Make the environments infinite: there is no a boundary.  Replace `ℕ`
--    locations with integers.  This is unnatural, too.
-- d. Make it an error, i.e. "Maybe-ize" movement.

-- Options b and c might be easier with `Fin`s rather than `ℕ`s as indexes.

--------------------
-- General-purpose

-- From an EnvMap, generate a list of EnvLocPairs.  The idea is to get the Envs
-- into a list so we can manipulate them using list operations, but since Envs
-- are indexed, we have to put the Envs into Sigma pairs in order to have a list
-- with a single element type.
envmap-to-envpairs : EnvMap → List (EnvLocPair)
envmap-to-envpairs envs = L.map (env-to-locpair ∘ Value.K&_.value) $ toList envs

-- Given a list of EnvLocPairs, extract the dunlins from the env.  The Duns from
-- a given Env have the same Loc as the Env, so they can be in a List.  But for
-- a comprehensive list of all dunlins or a list of lists of dunlins, we need to
-- wrap the dunlins in Sigma-pairs so that elements will all have the same type.
envpairs-to-dunspairs : List (EnvLocPair) → List (List DunLocPair)
envpairs-to-dunspairs [] = []
envpairs-to-dunspairs ((loc , env) ∷ xs) = L.map dun-to-locpair (env-duns env) ∷ envpairs-to-dunspairs xs

-- Given an EnvMap, extracts all of the dunlins in all of the envs, wraps them
-- in loc , dun Sigma pairs, and returns a list of those pairs.
collect-all-dunpairs : EnvMap → List DunLocPair
collect-all-dunpairs envs = L.concat $ envpairs-to-dunspairs $ envmap-to-envpairs envs

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

-- TODO: New dunlins shouldn't be required to all land in the same environgment..
-- Also, consider allowing different dunlins to have different reproductive strategies.
-- This could be implemented by putting a choose-loc field into Dun.

-- choose-child-loc is some function from each dunlin to a new location. This can 
-- account the dunlin's current location, the dunlin's id, or other internal state
-- of the dunlin.
reproduce : {loc : Loc} → (max-id : ℕ) → (num-childs : ℕ) → (choose-child-loc : (Dun loc) → ℕ) → (parent : Dun loc) → List (Dun loc)
reproduce _ 0 _ _ = []
reproduce max-id (suc n) choose-loc (short-beak _ loc) =
   iterate next-dun (short-beak (suc max-id) loc) (suc n)
reproduce max-id (suc n) choose-loc (long-beak _ loc) =
   iterate next-dun (long-beak  (suc max-id) loc) (suc n)
-- CHECK: Is max-id is getting incremented properly?

-- Calculates number of children from fitness of dun relative to env, and calls reproduce.
-- Parent is the last argument for curried application.
--   TODO: Probably should be Maybe-ized.  At present it returns an empty list when an env can't be found.  This can't be distinguished from the zero fitness case.
--   NOTE the key to making this work was (a) letting Agda decide how to pattern match on the pairs, and (b) adding {loc = loc₁} so that the final (short/long-beak id loc₁) arg would check.
reproduce-per-fit : {loc : Loc} → (max-id : ℕ) → (envs : EnvMap) → (fitfn : FitnessFn) → (choose-loc : Dun loc → ℕ) → (parent-pair : DunLocPair) → List (Dun loc)
reproduce-per-fit {loc = loc₁} max-id envs fitfn choose-loc (loc , parent@(short-beak id .loc))
    with lookup envs loc
... | nothing = []
... | just env = let fit = fitfn parent env
                 in if (fit ≡ᵇ 0) then [] else reproduce max-id fit choose-loc (short-beak id loc₁)
reproduce-per-fit {loc = loc₁} max-id envs fitfn choose-loc (loc , parent@(long-beak id .loc))
    with lookup envs loc
... | nothing = []
... | just env = let fit = fitfn parent env
                 in if (fit ≡ᵇ 0) then [] else reproduce max-id fit choose-loc (long-beak id loc₁)

--------------------
-- Death

-- TODO: -- Add removal of dead dunlins based on some criterion.


--==========================================================--
-- Niche construction, i.e. modification of environments due to
-- dunlins in them.

-- TODO
-- e-evolve 

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

d-evolve : {loc : Loc} → (max-id : ℕ) → EnvMap → (fitfn : FitnessFn) → (choose-loc : Dun loc → ℕ) → (ℕ × EnvMap)
d-evolve max-id envs fitfn choose-loc =
  let old-dunlins = collect-all-dunpairs envs  -- need to revise for indexed dunlins
      new-dunlins = L.concatMap (reproduce-per-fit max-id envs fitfn choose-loc) old-dunlins -- make baby dunlins
      new-max-id = max-id + (L.length new-dunlins) -- Is there be a better way?
  in (new-max-id , add-duns-to-envs new-dunlins envs)


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
     mildly-disturbed 1 (short-beak 2 1 ∷ short-beak 3 1 ∷ []))
    ∷
    (2 Data.Tree.AVL.Value., undisturbed 2 (short-beak 2 2 ∷ [])) ∷
    (3 Data.Tree.AVL.Value., mildly-disturbed 3 (long-beak 2 3 ∷ [])) ∷
    (4 Data.Tree.AVL.Value., well-disturbed 4 (long-beak 2 4 ∷ [])) ∷
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
