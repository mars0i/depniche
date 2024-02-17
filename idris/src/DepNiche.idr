module DepNiche

import Data.Vect

test : String
test = "Hello from Idris2!"

-- simple name-indexed niches
data Niche : String -> Type where
  MkNiche : (name : String) -> Niche name

-- how does this relate to a niche?
data Reproducer : Type where
  Reprod : Reproducer


data NicheN :  (Vect n Integer -> Nat) -> Vect n Integer -> Type where
  MkNicheN : (f : Vect n Integer -> Nat) -> (params : Vect n Integer) -> NicheN f params

-- dummy example
niche : NicheN Data.Vect.length [1,2,3]  -- without this, arg types are indeterminate
niche = MkNicheN length [1,2,3]

-- The number of offspring for a NReproducer is a function of its niche.
-- Specifically, the this number is the result of applying the niche's 
-- function from a vector of integer parameters to a Nat, to the params.
-- representing a number of 
data NReproducer : (noffspring : Nat) -> Type where
  MkNReproducer : (f : (Vect n Integer) -> Nat) ->
                  (niche : NicheN f params) -> 
                  NReproducer (f params)

-- dummy example using previous dummy val niche
reprod = MkNReproducer length niche
