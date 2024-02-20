module DepNiche2

-- import Data.Vect
import Data.List
-- import Decidable.Equality


data Niche : (idx : Nat) -> Type where
  MkNiche : (idx : Nat) -> Niche idx

-- These are types
Berries = MkNiche 0
Potatoes = MkNiche 1

{-
-- This errors:
niches : List Niche
niches = [Berries, Potatoes]
-- I can't make a list of types?
-- i.e. you can bring non-types into the type world, but not vice versa?

-- I wonder whether I can do this in Agda, with its universes.
-- i.e. have a type-list at one type level, but the types in it are at a
-- lower level?
-}

{-
-- I don't know why this doesn't work.  The idea is to create 
-- ("niche construct") a new Niche from an old one by incrementing
-- the index.
incNiche : Niche i0 -> Niche i1
incNiche (MkNiche i) = MkNiche (S i)
-}


record Riche where
  constructor MkRiche
  idx : Nat
