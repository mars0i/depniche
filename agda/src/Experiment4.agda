-- Exploring how to specify configuration of a model (a System) in order to write the Dstep and Estep functions.

module Experiment4 where

open import Niche
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

-- See docs/DunlinStory1.md for the rationale for the names and type constructors
-- or record fields below.

----------------------------------------------------------
-- Dun and Env records
-- These sort of correspond to the D and E defs in Niche.Example.

-- Note that the env and dunlins parameters are not Env or Dun;
-- they are id numbers.  (Disappointing to have to resort to this.)

data Beak : Set where
  thin : Beak
  thick : Beak

data Mud : Set where
  undisturbed : Mud
  mildly-disturbed : Mud
  well-disturbed : Mud

record Dun : Set where
  field
    id : ℕ
    beak : Beak
    env-id : ℕ

record Env : Set where
  field
    id : ℕ
    mud : Mud
    dunlin-ids : List ℕ

-- Useful for inputs and outputs to interactions between a dunlin and its env.
record DunEnvPair : Set where
  field
    dun : Dun
    env : Env

elsbeth = record {id = 0; beak = thin; env-id = 0}
emma    = record {id = 1; beak = thick; env-id = 1}
dex     = record {id = 2; beak = thin; env-id = 1}

west = record {id = 0; mud = mildly-disturbed; dunlin-ids = [ 0 ]}
east = record {id = 1; mud = undisturbed; dunlin-ids = 1 ∷ 2 ∷ []}

dunlins = elsbeth ∷ emma ∷ dex ∷ []
envs = west ∷ east ∷ []

----------------------

Dun-dec≡ : Dec≡ Dun
Dun-dec≡ record { id = id₁ ; beak = beak₁ ; env-id = env-id₁ }
         record { id = id₂ ; beak = beak₂ ; env-id = env-id₂ } = {!!}
-- I think I need an And operator here, and then And three Dec≡'s together?


-- ISSUE TO BE ADDRESSED: When there are multiple dunlins in an env
-- that are engaged in niche construction, do they make changes to the
-- env sequentially or in parallel?  Can one dunlin's effect accidentally
-- undo another's?  Maybe niche construction should be understood as a
-- collective effect of all dunlins in a given env.  But that the function
-- that calculates this update to the env could be very complex.
-- An alternative is to treat envs as microenvironments, s.t. each is
-- occupied by only a single dunlin.  However, in that case we need to
-- allow the possibility that changes in envs will bleed over to nearby envs.

d-evolve : ∀ (t : 𝕋) → (Eₜ : List Env) → (Dₜ : List Dun) → List Dun
d-evolve = {!!}

