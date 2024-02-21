module DepNiche2

-- import Data.Vect
import Data.List
-- import Decidable.Equality


data Niche : (idx : Nat) -> Type where
  MkNiche : (idx : Nat) -> Niche idx

-- These are types
Berries = MkNiche 0
Potatoes = MkNiche 1
Apples = MkNiche 1

-- This is a list of types!  However, they are the same type.
niches = the (List (Niche 1)) [Apples, Potatoes]

-- This won't work because (Niche 0) and (Niche 1) are different types.
-- badniches = [Berries, Potatoes]


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
