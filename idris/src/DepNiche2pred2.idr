-- based on DepNiche2predicate.idr, but cleaned up.
-- See that file for alternatives.
module DepNiche2pred2

data Niche : (x : Nat) -> Type where
  MkNiche : (x : Nat) -> Niche x

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
  ItIsNiche : (n : Nat) -> IsNiche (Niche n)

incNiche : (a : Type) -> IsNiche a => Type
incNiche .(Niche n) @{ItIsNiche n} = Niche (S n)
