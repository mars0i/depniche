/-! 
  What if niches were typeclasses?
-/

-- Can add methods that contribute information to construct
-- fitnesss or probabilities of survival or reproduction.

inductive Organism : (k : Nat) → Type where
  | mk : (k : Nat) → Organism k
deriving Repr

-- OK, I don't know how to do this, syntactically.  Seems like it should be
-- possible.  How do do the following properly?

-- class Niche (k : Nat -> (α : Type)) where

-- instance : Niche Nat.zero (Organism 0) where

-- This works, but now Niche isn't an indexed family
class Niche (α : Type) where
instance : Niche (Organism 3) where
