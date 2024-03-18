/-! 
  What if niches were typeclasses?
-/

inductive Organism : (k : Nat) → Type where
  | mk : (k : Nat) → Organism k
deriving Repr

-- inspired by ofNat,  https://lean-lang.org/functional_programming_in_lean/type-classes/pos.html
class Niche (_ : Nat) (α : Type) where
  fitness : Nat

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
