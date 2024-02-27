-- Kyle Miller's suggestion about how to do what I'm trying
-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Construct.20type.20from.20index.20in.20another.20type/near/423694347

structure Niche where
  k : Nat

structure Organism (k : Nat) where
  n : Nat
  deriving Repr

def Niche.type (n : Niche) : Type := Organism n.k

-- Make it automatic; turn a `Niche` into a type wherever it's used in a place expecting a type:
instance : CoeSort Niche Type := ⟨Niche.type⟩

-- organism-level niche incrementation: increment an organism's niche
def incOrganism {k : Nat} (o : Organism k) : Organism (k + 1) :=
  -- Syntax to reuse the fields for the new type:
  {o with}

-- Doesn't work.
/-- Generate a new niche from an old niche, incrementing the index. -/
def incNiche (n : Niche) : Niche  :=
  {k := n.k + 1}

def incOrganism' (n : Niche) (o : n) : incNiche n :=
  incOrganism o
