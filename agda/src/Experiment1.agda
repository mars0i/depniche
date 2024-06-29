-- Exploring how to specify configuration of a model (a System) in
-- order to write the Dstep and Estep functions.

-- See docs/DunlinStory1.md for the rationale for the names and type constructors
-- or record fields below.

module Experiment1 where

open import Niche
open import Function.Base
open import Data.List
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

-- Just for quick testing and experimentation
default-dun-tuple = make-dun-pair thin-beak 1000 1000
dunlin-head = exploding-head default-dun-tuple
dunlin-tail = exploding-tail default-dun-tuple

{- Tests
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

-- Just for quick testing and experimentation
default-env-tuple = make-env-pair undisturbed 1000 [ 1000 ]
env-head = exploding-head default-env-tuple
env-tail = exploding-tail default-env-tuple

envs = make-env-pair undisturbed 1 [ 1 ] ∷
       make-env-pair mildly-disturbed 2 (2 ∷ 3 ∷ [])∷
       env-to-pair (well-disturbed 3 []) ∷ []

{- TESTS
env1 = snd (env-head envs)
env2 = snd (env-head (env-tail envs))
env3 = snd (env-head (env-tail (env-tail envs)))
-}

SysListPair : (Set × Set)
SysListPair = (DunPairList ,′ EnvPairList)

------------------------------------------------------------
-- Define data structure for initial set of relationships between
-- dunlins and their environments

-- 8 envs, 4 dunlins


{-
dun-env-assocs : List (ℕ ×
                       ℕ → ℕ → Dun ℕ ℕ ×
                       List ℕ × 
                       ℕ → List ℕ → Env ℕ (List ℕ))
-}
dun-env-assocs = (0 ,′ thin-beak  ,′ [ 1 ] ,′ [ undisturbed ]) ∷
                 (1 ,′ thick-beak ,′ [ 2 ] ,′ [ mildly-disturbed ]) ∷
                 (2 ,′ thin-beak  ,′ [ 5 ] ,′ [ mildly-disturbed ]) ∷
                 (3 ,′ thick-beak ,′ [ 7 ] ,′ [ well-disturbed ]) ∷
                 []

make-duns-and-envs : List (ℕ × List ℕ) → DunPairList × EnvPairList
make-duns-and-envs = {!!}


{-
-- Why does this work, but a pair (or list) using DunPairList and EnvPairList doesn't?
make-duns-and-envs : List (Σ ℕ (λ x → Σ ((id₁ env : ℕ) → Dun id₁ env)
                                        (λ x₁ → Σ (List ℕ)
                                                  (λ x₂ → List ((id₁ : ℕ)
                                                                (dunlins : List ℕ) → Env id₁ dunlins)))))
make-duns-and-envs = {!!}
-}

{-
-- make-duns-and-envs : List (ℕ × List ℕ) → EnvPairList
-- make-duns-and-envs : List (ℕ × List ℕ) → SysListPair
-- make-duns-and-envs : List (Σ ℕ (λ x → Σ ((id₁ env : ℕ) → Dun id₁ env)
--                                         (λ x₁ → Σ (List ℕ)
--                                                   (λ x₂ → List ((id₁ : ℕ)
--                                                                 (dunlins : List ℕ) → Env id₁ dunlins)))))
-- Can't get this to work; I don't know why.  I'll use a list instead.
-- This shows that (DunPairList ,′ EnvPairList) can work ...
y : Set × Set
y = DunPairList ,′ EnvPairList
-- Literal, expanded version:
x : Set × Set
x = (List (Σ (Σ ℕ (λ x → ℕ)) (λ prod → Dun (Data.Product.Base.Σ.proj₁ prod) (snd prod)))) ,′ (List (Σ (Σ ℕ (λ x → List ℕ)) (λ prod → Env (Data.Product.Base.Σ.proj₁ prod) (snd prod))))

-- Doesn't work either.
make-duns-and-envs : List (ℕ × List ℕ) → DunPairList ∷ EnvPairList ∷ []
make-duns-and-envs = {!!}
-}

{-
make-duns : List (ℕ × List ℕ) → List DunPair
make-duns [] = []
make-duns (x ∷ xs) = let dun-id = fst x
                         dun-constructor = snd x
                         env-ids = fst (snd x)

                     in [ make-dun-pair dun-id env-ids ]
-}

{-
-- This is supposed to be used to initialize a system, but
-- I haven't thought through the next steps.
record DunEnvsPair : Set where
  field
    dunidx : ℕ
    envidxs : List ℕ

DunEnvsAssocs : Set
DunEnvsAssocs = List DunEnvsPair
-}
