-- based on DepNiche2predicate.idr, but cleaned up.
-- See that file for alternatives.
module DepNiche2pred

data Niche : (x : Nat) -> Type where
  MkNiche : (x : Nat) -> Niche x

data IsNiche : Type -> Type where
  ItIsNiche : IsNiche (Niche x)

incNiche0 : (a : Type) -> {auto 0 prf : IsNiche a} -> Type
incNiche0 (Niche x) @{ItIsNiche} = Niche (S x)
incNiche0 _ = Void


partial
incNiche1 : (a : Type) -> (prf : IsNiche a) -> Type
incNiche1 (Niche x) ItIsNiche = Niche (S x)

partial
incNiche2 : (prf : IsNiche a) -> (a : Type) -> Type
incNiche2 ItIsNiche (Niche x) = Niche (S x) 

partial
incNiche3 : (a : Type) -> {prf : IsNiche a} -> Type
incNiche3 (Niche x) {prf = ItIsNiche} = Niche (S x) 

partial
incNiche4 : {prf : IsNiche a} -> (a : Type) -> Type
incNiche4 {prf = ItIsNiche} (Niche x) = Niche (S x) 


-- creek = Niche 0
-- beaverpond = incNiche creek

-- oldniches : List Type
-- oldniches = [Niche 0, Niche 1]

-- newniches : List Type
-- newniches = [incNiche (Niche 0) @{ItIsNiche}, incNiche @{ItIsNiche} (Niche 1)] -- Note the proof argument can go in either order
