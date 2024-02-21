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

-- What can I do with this type?
DNiche = (n : Nat ** Niche n)
-- note DPair is already in the prelude, so don't use a name like that.

{-
-- THIS WORKS!  This is, sortof, a list of niches that are different.

DepNiche2> the (List DNiche) [(1 ** MkNiche 1), (2 ** MkNiche 2), (3 ** MkNiche 3)]
[(1 ** MkNiche 1), (2 ** MkNiche 2), (3 ** MkNiche 3)] : List (n : Nat ** Niche n)

-- IS it a list of Types?   I don't think so.  It's a list of niches in dep pairs.
-- DNiche is a type.  (n : Nat ** Niche n) is a type.  But since (MkNiche 2) is 
-- an instance of Niche 2, I think (2 ** MkNiche 2) is an instance of DNiche.
-- Compare:

DepNiche2> the (List Nat) [1, 2, 3]
[1, 2, 3] : List Nat

(If a list of types isn't possible in Idris, it has to be possible in Agda.)

-}

-- Note \n doesn't bind the n in the dep pair, here:
{-
DepNiche2> (\n => (n : Nat ** Niche n)) 3
(n : Nat ** Niche n) : Type
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
