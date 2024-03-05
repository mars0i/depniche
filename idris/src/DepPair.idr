-- Wondering if using dependent pairs would allow pattern matching
-- on (pairs containing) types in languages without type-case, but
-- trying it first in Idris where it's probably easier.
--
-- Based on DepNiche4: see that file for additional examples
--
module DepPair


data Niche : (k : Nat) -> Type where
  User : (k : Nat) -> Niche k

-- increment niche users
incuser : Niche k -> Niche (S k)
incuser (User k) = User (S k)

-- This is impossible because the users have different types.
-- I would need a custom data structure for this purpose.
--   organisms = [org1, org2]

-- increment niches themselves
-- simple version with kudgey hack to make it covering
incNiche0 : Type -> Type
incNiche0 (Niche k) = Niche (S k)
incNiche0 _ = Void

-- kiana's version to get rid of not covering error:
-- https://discord.com/channels/827106007712661524/1210312619886645338/1211191154352193576
data IsNiche : Type -> Type where
  ItIsNiche : (k : Nat) -> IsNiche (Niche k)

-- increment niches themselves
-- with complicated hack to convince Idris it only applies to Niches--see link above
incNiche : (a : Type) -> IsNiche a => Type
incNiche .(Niche k) @{ItIsNiche k} = Niche (S k)

---------------

data IsNiche1 : Type -> Type where
  ItIsNiche1 : {k : Nat} -> IsNiche1 (Niche k)

incNiche1 : (a : Type) -> IsNiche1 a => Type
incNiche1 .(Niche k) @{ItIsNiche1} = Niche (S k)

----------------

nichepair : Nat -> (Nat ** Type)
nichepair k = (k ** Niche k)

np = nichepair 5
