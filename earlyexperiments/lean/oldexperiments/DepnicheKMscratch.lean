-- Kyle Miller's suggestion about how to do what I'm trying
-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Construct.20type.20from.20index.20in.20another.20type/near/423694347

structure Niche where
  k : Nat
  deriving Repr

#check Niche
#check Niche.k

-- I guess Organism has both a type index k, and a field n.
-- As noted below, this allows these two values to diverge, which
-- is not what I want.  I think I might need a proof to keep them
-- in sync.  (Dependent pairs does that for me.)
structure Organism (k : Nat) where
  n : Nat
  deriving Repr

#check Organism
#check Organism.n
-- #check Organism.k  -- fails

-- This doesn't exactly add a field to Niche (?); it creates a new 
-- variable type in the Niche "namespace".  The value of this variable
-- is a function from a Niche n to a type which is an Organism. 
-- i.e. In the Niche namespace, there is a function named "type" such
-- that given a Niche, extracts the k field in the Niche, and creates
-- an organism with that same k as its index.
-- I think Kyle misunderstood, and this is backwards.  
-- Niche and Organism should be swapped.
def Niche.type (n : Niche) : Type := Organism n.k

#check Niche.type
#check (Niche.type)
#check Organism.mk 
#check (Organism.mk) 
def o : Organism 3 := Organism.mk 5
#check o
#eval o
#check o.n
#eval o.n
-- So Kyle's scheme allows the organism index and the field to diverge,
-- which is not what I want.  The field is just supposed to make it easy
-- (or rather possible) to get at the index.
-- I need this in Niche as well--that's what will emulate typecase.

#check CoeSort

-- Make it automatic; turn a `Niche` into a type wherever it's used in a place expecting a type:
instance : CoeSort Niche Type := ⟨Niche.type⟩


---------------------------------------------

-- organism-level niche incrementation: increment an organism's niche
def incOrganism {k : Nat} (o : Organism k) : Organism (k + 1) :=
  -- Syntax to reuse the fields for the new type:
  {o with}

/-- Generate a new niche from an old niche, incrementing the index. -/
def incNiche (n : Niche) : Niche  :=
  {k := n.k + 1}

def incOrganism' (n : Niche) (o : n) : incNiche n :=
  incOrganism o
