-- Kyle Miller's suggestion about how to do what I'm trying
-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Construct.20type.20from.20index.20in.20another.20type/near/423694347

structure User where
  k : Nat

structure Niche (k : Nat) where
  n : Nat
  deriving Repr

def User.type (n : User) : Type := Niche n.k

-- Make it automatic; turn a `User` into a type wherever it's used in a place expecting a type:
instance : CoeSort User Type := ⟨User.type⟩

-- organism-level niche incrementation: increment an organism's niche
def incNiche {k : Nat} (o : Niche k) : Niche (k + 1) :=
  -- Syntax to reuse the fields for the new type:
  {o with}

/-- Generate a new niche from an old niche, incrementing the index. -/
def incUser (n : User) : User  :=
  {k := n.k + 1}

def incNiche' (n : User) (o : n) : incUser n :=
  incNiche o

