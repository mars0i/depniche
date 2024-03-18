/-! 
  What if niches were typeclasses?
-/

inductive Organism : (k : Nat) → Type where
  | mk : (k : Nat) → Organism k
deriving Repr

-- inspired by ofNat,  https://lean-lang.org/functional_programming_in_lean/type-classes/pos.html
class Niche (_ : Nat) (a : Type) where
  fitness : Nat

-- This doesn't make instances of Organism k have type Niche j, for any j.
instance : Niche m (Organism n) where  -- m is the Niche parameter
  fitness := m * n  -- Silly fitness fn, but shows can be function of both types

#check (Niche.fitness)


-- Define an organism
def o1 := Organism.mk 5
#check o1
#eval o1

-- Calculate an organism's fitness in a given niche
def o1fit := Niche.fitness 3 (Organism 5)
#check o1fit
#eval o1fit

-- Evaluate the fitness of the same organism type in different Niches:
#eval Niche.fitness 2 (Organism 5)
#eval Niche.fitness 4 (Organism 5)

-- Connect this to organism instances:
def ofit (_ : Organism n) (m : Nat) : Nat := Niche.fitness m (Organism n)

-- fitness of o1 in Niche 3:
#check ofit o1 3
#eval ofit o1 3

-- fitness of o1 in Niche 4:
#check ofit o1 4
#eval ofit o1 4

-- Note we're not passing around niches, just niche parameters.
-- Seems silly, in terms of this code alone, to bother with the typeclass.
-- But fits with Naïm's suggestion to use niche parameters as universe codes.

----------------------------------------------------

-- This is for an organism, not a type, as its second argument:
class Niche2 (_ : Nat) (a : Organism n) where
  fitness : Nat

def o2 := Organism.mk 11
#check o2

-- individual-organism-specific fitness function
instance : Niche2 3 (o2 : Organism 11) where
  fitness := 3 + 11 -- can't do this properly without type-case

-- Then this works:
#eval Niche2.fitness 3 o2

-- But this fails, because we haven't defined an instance for Niche2 3 for o2:
-- #eval Niche2.fitness 4 o2

instance : Niche2 4 (o2 : Organism 11) where
  fitness := 4 + 11 -- can't do this properly without type-case

-- But now it works:
#eval Niche2.fitness 4 o2
