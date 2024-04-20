module DepNiche2mwe

data Niche : (idx : Nat) -> Type where
  MkNiche : (idx : Nat) -> Niche idx

-- partial
incNiche : Type -> Type
incNiche (Niche x) = Niche (S x) 
incNiche _ = ()
-- incNiche _ = Void

newniches : List Type
newniches = map incNiche [Niche 0, Niche 1]
-- = [Niche 1, Niche 2] : List Type
