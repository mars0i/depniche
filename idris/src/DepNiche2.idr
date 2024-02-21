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
-- Note DPair is already in the prelude, so don't use a similar name.

-- THIS WORKS!  This is, sortof, a list of niches that are different.
deniches = the (List DNiche) [(1 ** MkNiche 1), (2 ** MkNiche 2), (3 ** MkNiche 3)]
-- IS it a list of Types?   I don't think so.  It's a list of niches in dep pairs.
-- DNiche is a type.  (n : Nat ** Niche n) is a type.  But since (MkNiche 2) is 
-- an instance of Niche 2, I think (2 ** MkNiche 2) is an instance of DNiche.

danums = the (List Nat) [1, 2, 3]

-- (If a list of types isn't possible in Idris, it has to be possible in Agda.)

-- But check this out:
disniche = [DNiche] -- [(n : Nat ** Niche n)] : List Type

datniche = [Niche 5]
-- [Niche 5] : List Type

datypes = [Nat, Int, Integer, String, Niche 3, (Niche 4)]
-- [Nat, Int, Integer, String, Niche 3, Niche 4] : List Type

partial -- needed because it doesn't work with all types!
incType : Type -> Type
incType (Niche x) = Niche (S x) 

daniches : List Type -- needed to make e.g. map work
daniches = [Niche 1, Niche 2]

-- This works!  But you need partial--not sure why
partial
incedniches : List Type
incedniches = map incType daniches -- [Niche 2, Niche 3] : List Type

-- Call these things List Types seems wrong.  They are more specific.
-- Surely I can do more in Agda or Lean.
