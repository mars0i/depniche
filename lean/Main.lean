-- import «Depniche»

def yo : String := " this"

def f (x : Nat) : Nat := x + 1

def f5 : Nat := f 5

-- inductive Niche (k : Nat) where
--   | user : Nat → Niche k

@[match_pattern] -- ??
inductive Niche (k : Nat) where
  | user : Nat → Niche k
deriving Repr

def organism : Niche 5 := Niche.user 5
def niche : Type := Niche 5


-- organism-level niche incrementation: increment an organism's niche
def incOrganism (o : Niche k) : Niche (1 + k) :=
  match o with
  | Niche.user k => Niche.user (1 + k)

#eval organism
#eval incOrganism organism

#check Niche
#check (Niche 4)

-- cf. https://proofassistants.stackexchange.com/questions/2438/why-can-addition-be-used-in-pattern-matching-nats-but-not-multiplication
-- attribute [match_pattern] Niche 
-- attribute [match_pattern] Niche k

-- Generate a new niche from an old niche, incrementing the index.
-- Doesn't work.
def incNiche {k : Nat} (n : Type) : Type :=
  match n with
  | (Niche k) => Niche (1 + k)



def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
