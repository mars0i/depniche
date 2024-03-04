module DepNiche4

data Niche : (k : Nat) -> Type where
  MkUser : (k : Nat) -> Niche k

-- increment niche users
incuser : Niche k -> Niche (S k)
incuser (MkUser k) = MkUser (S k)

org1 = MkUser 3
org2 = incuser org1

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

-- This is possible because every (Niche k) is an instance of the same type, viz. Type:
someNiches : List Type
someNiches = [Niche 3, Niche 4]

-- map won't work here because of the complexity of incNiche; need to define a specialized functor.
otherNiches : List Type
otherNiches = [incNiche (Niche 3), incNiche (Niche 4)]

-- But map works with the simple version:
otherNiches0 : List Type
otherNiches0 = map incNiche0 someNiches

---------
-- variations

data IsNiche1 : Type -> Type where
  ItIsNiche1 : {k : Nat} -> IsNiche1 (Niche k)

incNiche1 : (a : Type) -> IsNiche1 a => Type
incNiche1 .(Niche k) @{ItIsNiche1} = Niche (S k)


{-
-- non-working attempt
data IsNiche2 : Type -> Type where
  ItIsNiche2 : {k : Nat} -> IsNiche2 (Niche k)

incNiche2 : {auto 0 prf : IsNiche2 a} -> (a : Type) -> Type
incNiche2 @{ItIsNiche2} (Niche k) = Niche (S k)
-}

