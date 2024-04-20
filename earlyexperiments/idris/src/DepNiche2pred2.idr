-- based on DepNiche2predicate.idr, but cleaned up.
-- See that file for alternatives.
module DepNiche2pred2

data Niche : (k : Nat) -> Type where
  MkNiche : (k : Nat) -> Niche k

isniche : (n : Niche k) -> Niche (S k)
isniche (MkNiche k) = MkNiche (S k)

{-
data IsNiche : Type -> Type where
  ItIsNiche : IsNiche (Niche n)

-- not covering:
incNiche : (a : Type) -> IsNiche a => Type
incNiche (Niche x) @{ItIsNiche} = Niche (S x)
-}

-- kiana's version to get rid of not covering error:
-- https://discord.com/channels/827106007712661524/1210312619886645338/1211191154352193576
data IsNiche : Type -> Type where
  ItIsNiche : (k : Nat) -> IsNiche (Niche k)

incNiche : (a : Type) -> IsNiche a => Type
incNiche .(Niche k) @{ItIsNiche k} = Niche (S k)
