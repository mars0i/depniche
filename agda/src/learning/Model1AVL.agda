module learning/Model1AVL where

-- open import Agda.Builtin.Sigma
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Function.Base
open import Data.Bool
open import Data.List as L using (List; _∷_; []; [_]; iterate; _++_; map; concat; concatMap; zipWith; _[_]%=_; _[_]∷=_)
open import Data.Vec as V using (Vec; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base -- using (_×_; _,′_) -- Needs stdlib 2.0
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Niche
open import Kludges

data Dun : Set where
  short-beak   : (id : ℕ) → (loc : ℕ) → Dun
  long-beak  : (id : ℕ) → (loc : ℕ) → Dun

-- An abbreviation for the type of the Dun constructors will be useful later.
DunConstr : Set 
DunConstr = (i : ℕ) → (e : ℕ) → Dun

new-dun : DunConstr → (env-id : ℕ) → (max-id : ℕ) → Dun
new-dun constr env-id max-id = constr (suc max-id) env-id

-- For use inside List.iterate and similar functions to generate a
-- sequence of dunlins with consequitive (presumably new) ids.
next-dun : Dun → Dun
next-dun (short-beak id loc) = short-beak (suc id) loc
next-dun (long-beak id loc) = long-beak (suc id) loc

-- projection operators

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

data Env : Set where
  undisturbed      : (dunlins : List Dun) → (loc : ℕ) → Env
  mildly-disturbed : (dunlins : List Dun) → (loc : ℕ) → Env
  well-disturbed   : (dunlins : List Dun) → (loc : ℕ) → Env

-- An abbreviation for the type of the Env constructors will be useful later.
EnvConstr : Set
EnvConstr = (dunlins : List Dun) → (loc : ℕ) → Env

-- projection operators
env-params : Env → (ℕ × List Dun)
env-params (undisturbed dunlins loc) = (loc , dunlins)
env-params (mildly-disturbed dunlins loc) = (loc , dunlins)
env-params (well-disturbed dunlins loc) = (loc , dunlins)

env-loc : Env → ℕ
env-loc (undisturbed _ loc) = loc
env-loc (mildly-disturbed _ loc) = loc
env-loc (well-disturbed _ loc) = loc

env-duns : Env → List Dun
env-duns (undisturbed dunlins _) = dunlins
env-duns (mildly-disturbed dunlins _) = dunlins
env-duns (well-disturbed dunlins _) = dunlins

-- Is this non-idiomatic?
env-constructor : Env → EnvConstr
env-constructor (undisturbed _ _) = undisturbed
env-constructor (mildly-disturbed _ _) = mildly-disturbed
env-constructor (well-disturbed _ _) = well-disturbed

DunEnvAssocs : Set
DunEnvAssocs = List ((List ℕ × List DunConstr) × (ℕ × EnvConstr)) 
--                    dun ids                     loc


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

-- Creates a list of environment Sigma-pairs from the assocs.
assocs-to-envs : DunEnvAssocs → List Env
assocs-to-envs [] = []
assocs-to-envs (x ∷ xs) = let ((dun-ids , dun-constrs) , (loc , env-constr)) = x
                              duns = zipWith (λ id constr → (constr id loc)) dun-ids dun-constrs
                          in (env-constr duns loc) ∷ assocs-to-envs xs

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


-- The first element of each top level pairs in these lists is just there
-- to allow different types to live in the same list.  When processing
-- the envs or dunlins, it can be ignored (but might need to be recreated to
-- make the next set of envs and dunlins.
all-envs = assocs-to-envs dun-env-assocs
all-duns = assocs-to-duns dun-env-assocs


-----------------------------------------------------------------------------
-- experiment.  See CatMap, which is based on
-- https://agda.github.io/agda-stdlib/v2.0/README.Data.Tree.AVL.html

open import Data.Nat.Properties using (<-strictTotalOrder)

{-
import Data.Tree.AVL.Map as M
open M <-strictTotalOrder

EnvMap = Map Env

empty-env-map = M.empty
singleton-env-map = M.singleton 5 (undisturbed 1 [])
-}

{-
import Data.Tree.AVL.IndexedMap
open Data.Tree.AVL.IndexedMap -- <-strictTotalOrder

EnvMap = Map (ℕ × Env)
-}

--empty-map : Map 
--empty-map = empty

{-
import Data.Tree.AVL
open Data.Tree.AVL  <-strictTotalOrder
open import Relation.Binary.PropositionalEquality -- for subst, at least

-- Define my map type
-- EnvAVL = Tree (MkValue (Vec Env) (subst (Vec Env)))
EnvAVL = Tree (MkValue (Vec Env) (subst (Vec Env)))

empty-env-map : EnvAVL
empty-env-map = empty

singleton-env-map : EnvAVL
singleton-env-map = singleton 1 ((undisturbed [] 1) ∷ [])
-- size singleton-env-map
just-env1 = lookup singleton-env-map 1
nada = lookup singleton-env-map 42

-- Overwrites old element 1:
singleton-env-map2 : EnvAVL
singleton-env-map2 = insert 1 ((mildly-disturbed [] 2) ∷ []) singleton-env-map
just-env2 = lookup singleton-env-map2 1
-- size singleton-env-map2

-- Why is this complaining that the nil does not have size 2?
-- Isn't the second arg a key?
-- (And I still don't know why I have to wrap the vals in a Vec.)
{-
two-envs-map : EnvAVL
two-envs-map = insert 2 ((well-disturbed 3 []) ∷ []) empty
-}
-- Well note that in the AVL README, the singleton avl t₁ is created with a
-- vector of length 2, and the first arg to the singleton is 2.
-- Look also at the fromList example further down.  The keys correspond
-- to the lengths of the vectors.  It may be relevant that the keys
-- are parameters of the vectors.
-- Maybe it's that (subst (Vec String)) means substitute the next arg
-- of Vec, i.e. the Nat or Fin.  So can I do that with Env locs?

env-pairs : List (ℕ × Env)
env-pairs = L.map (λ e → (env-loc e) , e) all-envs

env-map : EnvAVL
env-map = fromList {!!} -- Data.Tree.AVL.fromList env-pairs
-}
