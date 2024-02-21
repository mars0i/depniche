module dep-niche0 where

open import nat
open import integer
open import string
open import vector

test : string
test = "Hello from Idris2!"

-- simple name-indexed niches
data Niche : Set where
  MkNiche : (name : string) -> Niche

-- how does this relate to a niche?
data Reproducer : Set where
  Reprod : Reproducer

-- Doesn't check. urgh.  Agda. Why not?
data NicheN :  ∀ {n : ℕ} → (𝕍 n ℤ → ℕ) → 𝕍 n ℤ → Set where
  MkNicheN : {n : ℕ} → (f : 𝕍 n ℤ → ℕ) → (params : 𝕍 n ℤ) → NicheN f params

-- The number of offspring for a NReproducer is a function of its niche.
-- Specifically, the this number is the result of applying the niche's 
-- function from a vector of integer parameters to a Nat, to the params.
-- representing a number of 
data NReproducer : (noffspring : ℕ) -> Set where
  MkNReproducer : ∀ {n : ℕ} → ∀ {params : 𝕍 n ℤ} →
                 (f : (𝕍 n ℤ) → ℕ) → (niche : NicheN f params) →
                 NReproducer (f params)



