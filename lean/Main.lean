import «Depniche»

def yo : String := " this"

def f (x : Nat) : Nat := x + 1

def f5 : Nat := f 5

-- inductive Niche (k : Nat) where
--   | user : Nat → Niche k

inductive Niche (k : Nat) where
  | user : Nat → Niche k
deriving Repr

def organism : Niche 5 := Niche.user 5
def niche : Type := Niche 5
-- def niche2 : Type 1 := Niche 5


-- organism-level niche incrementation: increment an organism's niche
def incOrganism (o : Niche k) : Niche (1 + k) :=
  match o with
  | Niche.user k => Niche.user (1 + k)

#eval organism
#eval incOrganism organism

#check fun x => x

-- Generate a new niche from an old niche, incrementing the index.
-- Doesn't work.
def incNiche {k : Nat} (n : Type 1) : Type 1 :=
  match n with
  | Niche k => Niche (1 + k)



def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
