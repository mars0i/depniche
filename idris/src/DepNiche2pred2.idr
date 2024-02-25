-- based on DepNiche2predicate.idr, but cleaned up.
-- See that file for alternatives.
module DepNiche2pred2

data Niche : (x : Nat) -> Type where
  MkNiche : (x : Nat) -> Niche x

data IsNiche : Type -> Type where
  ItIsNiche : IsNiche (Niche n)

incNiche : (a : Type) -> IsNiche a => Type
incNiche .(Niche x) @{ItIsNiche} = Niche (S x)

