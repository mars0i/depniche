

@[match_pattern] -- added because of error message on inNiche,
                 -- but don't understand
inductive Niche (k : Nat) where
  | organism : Nat → Niche k
deriving Repr

-- organism-level niche incrementation: increment an organism's niche
def incOrganism (o : Niche k) : Niche (1 + k) :=
  match o with
  | Niche.organism k => Niche.organism (1 + k)

#check Niche
#check (Niche 4)

-- attribute [match_pattern] Niche 
-- attribute [match_pattern] Niche k

-- Generate a new niche from an old niche, incrementing the index.
-- Doesn't work.
def incNiche {k : Nat} (n : Type) : Type :=
  match n with
  | (Niche k) => Niche (1 + k)
