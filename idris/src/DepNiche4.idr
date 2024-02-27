module DepNiche4

data Niche : (k : Nat) -> Type where
  MkUser : (k : Nat) -> Niche k

-- kiana's version to get rid of not covering error:
-- https://discord.com/channels/827106007712661524/1210312619886645338/1211191154352193576
data IsNiche : Type -> Type where
  ItIsNiche : (k : Nat) -> IsNiche (Niche k)

-- increment niche users
incuser : Niche k -> Niche (S k)
incuser (MkUser k) = MkUser (S k)

org1 = MkUser 3
org2 = incuser org1

-- This is impossible because the users have different types.
-- I would need a custom data structure for this purpose.
--   organisms = [org1, org2]

-- increment niches themselves
incNiche : (a : Type) -> IsNiche a => Type
incNiche .(Niche k) @{ItIsNiche k} = Niche (S k)

-- This is possible because every (Niche k) is an instance of the same type, viz. Type:
someNiches : List Type
someNiches = [Niche 3, Niche 4]

-- map won't work here because of the complexity of incNiche.
-- Need to define a functor.
otherNiches : List Type
otherNiches = [incNiche (Niche 3), incNiche (Niche 4)]
