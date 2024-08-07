{-# OPTIONS --allow-unsolved-metas #-}
-- Temporary: allow importing this file despite open holes in it.

module Niche where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
-- open import Data.Nat
open import Data.Product
-- open import Data.Fin
open import Data.String
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

-- Key to Marshall's comments:
--    --?  General question about what code is doing, etc.
--    ---? Possibly ignorant novice Agda question about syntax, semantics, etc.
--    --   What it always means, but may include ignorant clarifications.


-- helpers (probably in std-lib _somewhere_)

--? I need some help understanding the following two definitions,
--? their purpose, and the applications below in the example section.
--? I think I'm partially familiar with related ideas from Idris, I think,
--? but not enough.  Checking the source for `Dec`, `yes`, and
--? `no` in the source is not sufficiently helpful at this stage.

-- This function of a type returns a type.
Dec≡ : (A : Set) → Set
Dec≡ A = (a b : A) → Dec (a ≡ b)

is-in : {A : Set} → (Dec≡ A) → (a : A) → List A → Bool
is-in dec a [] = false
is-in dec a (b ∷ as) with dec a b
... | yes _ = true
... | no _ = false


-- 𝕋, intended to represent discrete time
𝕋 : Set
𝕋 = ℕ


-- passage of time
tick : 𝕋 → 𝕋
tick = suc

-- Module parameterized by dunlins and envs
module System (DunlinNames : Set) (EnvNames : Set) where
  record SysMaker : Set₁ where  -- 
    field
      E₀ : List EnvNames      -- E₀ because these are the envs at t0, i.e. the initial time
      D₀ : List DunlinNames
      Estep : ∀ (t : 𝕋) → (Eₜ : List EnvNames) → (Oₜ : List DunlinNames) → List EnvNames
      Dstep : ∀ (t : 𝕋) → (Eₜ : List EnvNames) → (Oₜ : List DunlinNames) → List DunlinNames
    

  --? a History is/was the state of the system at t?
  --? Is this correct? To make a history, we write something like
  --?    History f1 f2
  --? where f1 is a function from times to lists of envs
  --?   and f2 is a function from times to lists of dunlins
  --? Is there a reason to do this with functions rather than some
  --?  sort of vector/array structure?

  record History : Set₁ where
    field
      Env    : (t : 𝕋) → List EnvNames
      Dunlin : (t : 𝕋) → List DunlinNames
--      Params : Set

  mkSys :
    (Params : Set) →
    SysMaker →
    History
  mkSys P Sys = record {
    Env    = E-fam ;  -- a function from time t to the next envs; calls Estep on the envs, dunlins at t.
    Dunlin = D-fam    -- ditto for dunlins
    }
    where  
      open SysMaker Sys

      -- Interspersed type signatures for mutual recursion:
      D-fam : (t : 𝕋) → List DunlinNames
      E-fam : (t : 𝕋) → List EnvNames

      D-fam zero = D₀   -- at t₀ return initial list of dunlins from SysMaker
      D-fam (suc t) = Dstep t (E-fam t) (D-fam t)
      -- at other t's make new dunlins using step fn from SysMaker

      E-fam zero = E₀   -- at t₀ return initial list of subenvs from SysMaker
      E-fam (suc t) = Estep t (E-fam t) (D-fam t)
      -- at other t's make new subenvs using step fn from SysMaker


-- List syntax: `[]` works, `[ 5 ]` works.  After that, have to use
-- Unicode double-colon \:: .
-- Note that the brackets after Σ below are special sigma-pair syntax.

module Example where

  --? I think the next two definitions allow proving that two strings are equal,
  --? but I'm confused about how they work. (Were these here for an initial example,
  --? but aren't needed now?)

  --? i.e. given a string, there's a string that its equal to?
  `_ : String → Set  -- note prefix operators
  `_ str = Σ[ a ∈ String ] a ≡ str

  --? This lets us input a string, and get back a dep pair with a proof
  --? that it's a string, with a type that requires that proof?
  ↑_ : (s : String) → ` s
  ↑ s = s , refl

  data D : Set where
    grey brown : D

  -- Without this, is there no sense of equality between constructors?
  -- Or is it just that it's better to be able to prove it?
  D-dec≡ : Dec≡ D
  D-dec≡ grey grey = yes refl 
  D-dec≡ grey brown = no (λ ()) -- () is the absurd pattern
  D-dec≡ brown grey = no (λ ())
  D-dec≡ brown brown = yes refl
  ---? Why (λ ()) ?  Is that a function of no arguments that then returns
  ---? the absurd pattern, or that short-circuits at () once it's invoked?
  ---? This is instead of () because Σ expects a function?
  ---? I thought (λ _ → ⊥) would work there, but it doesn't type check even if
  ---? I add `open import Data.Empty with (⊥)`:
  ---?    Set !=< ⊥
  ---?    when checking that the expression ⊥ has type ⊥
  ---? I think that means my function is returning a value where a type
  ---? is needed?

  D-is-in : (d : D) → List D → Bool
  D-is-in = is-in D-dec≡    -- D-dec≡ = (Dec≡ D)

  data E : Set where
    nest  no-nest : E

  E-dec≡ : Dec≡ E
  E-dec≡ nest nest = yes refl
  E-dec≡ nest no-nest = no (λ ())
  E-dec≡ no-nest nest = no (λ ())
  E-dec≡ no-nest no-nest = yes refl

  E-is-in : (e : E) → List E → Bool
  E-is-in = is-in E-dec≡

  open System D E
  
  -- TODO: define fitness functions for each dunlin-in-env for use here.
  --? Q: Why does t need to be an argument? The same rule applies in every timestep.
  d-evolve :  ∀ (t : 𝕋) → (Eₜ : List E) → (Dₜ : List D) → List D
  d-evolve t (no-nest ∷ []) Dₜ  = [ brown ]
  d-evolve t (nest ∷ []) Dₜ  =  [ grey ]
  d-evolve t (no-nest ∷ nest ∷ []) Dₜ  =  grey ∷ brown ∷ []
  d-evolve t Eₜ Dₜ  =  Dₜ

  
  -- TODO: define niche-construction function so that when there's
  -- a particular kind of dunlin in a particular kind of env, the
  -- env is sometimes modified/replaced.  Or just build that into e-evolve.
  --? Q: Why does t need to be an argument? The same rule applies in every timestep.
  e-evolve :  ∀ (t : 𝕋) → (Eₜ : List E) → (Dₜ : List D) → List E
  e-evolve t Dₜ [] = [ no-nest ]
  e-evolve t Dₜ (grey ∷ ds) = {!!}
  e-evolve t Dₜ (brown ∷ ds) = {! !}

  example-mk : SysMaker
  example-mk = 
    record { 
      E₀ = [ nest ]  ; 
      D₀ = [ grey ] ; 
      Estep = e-evolve ; 
      Dstep = d-evolve 
    }
