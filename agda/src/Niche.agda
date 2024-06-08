module Niche where

open import Data.Nat
open import Data.Product
open import Data.Fin
open import Data.String
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

-- Key to Marshall's comments:
--    --?  Means general question about what code is doing, etc.
--    ---? Means possibly ignorant novice Agda question about syntax, semantics, etc.
--    --   Means what it always does, but may include clarifications of what's obvious :-)

-- helpers (probably in std-lib _somewhere_)

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

module System (DunlinNames : Set) (EnvNames : Set) where
  record SysMaker : Set₁ where
    field
      E₀ : List EnvNames
      D₀ : List DunlinNames
      Estep : ∀ (t : 𝕋) → (Eₜ : List EnvNames) → (Oₜ : List DunlinNames) → List EnvNames
      Dstep : ∀ (t : 𝕋) → (Eₜ : List EnvNames) → (Oₜ : List DunlinNames) → List DunlinNames
    

  --? a History is/was the state of the system at t
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
    Env    = E-fam ;
    Dunlin = D-fam
    }
    where  
      ---? I guess a where clause can define a number of values, in this case
      ---? two functions D-fam and E-fam, which made values of Env and Dunlin
      ---? in record def above.

      open SysMaker Sys  ---? I assume makes unqualified record fields available

      ---? These must be type signatures for defs below. I didn't know you could
      ---? intersperse signatures before definitions in this way.
      D-fam : (t : 𝕋) → List DunlinNames
      E-fam : (t : 𝕋) → List EnvNames

      D-fam zero = D₀   -- at t₀ return initial list of dunlins from SysMaker
      D-fam (suc t) = Dstep t (E-fam t) (D-fam t)
      -- at other t's make new dunlins using step fn from SysMaker

      E-fam zero = E₀   -- at t₀ return initial list of subenvs from SysMaker
      E-fam (suc t) = Estep t (E-fam t) (D-fam t)
      -- at other t's make new subenvs using step fn from SysMaker


module Example where
  `_ : String → Set  -- note the prefix operators
  `_ str = Σ[ a ∈ String ] a ≡ str

  ↑_ : (s : String) → ` s
  ↑ s = s , refl


  data D : Set where
    grey brown : D

  D-dec≡ : Dec≡ D
  D-dec≡ grey grey = yes refl
  D-dec≡ grey brown = no (λ ())
  D-dec≡ brown grey = no (λ ())
  D-dec≡ brown brown = yes refl

  D-is-in : (d : D) → List D → Bool
  D-is-in = is-in D-dec≡

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
  
  d-evolve :  ∀ (t : 𝕋) → (Eₜ : List E) → (Dₜ : List D) → List D
  d-evolve t (no-nest ∷ []) Dₜ  = [ brown ]
  d-evolve t (nest ∷ []) Dₜ  =  [ grey ]
  d-evolve t (no-nest ∷ nest ∷ []) Dₜ  =  grey ∷ brown ∷ []
  d-evolve t Eₜ Dₜ  =  Dₜ

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
