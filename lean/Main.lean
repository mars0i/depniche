import «Depniche»

def yo : String := " this"

def f (x : Nat) : Nat := x + 1

def f5 : Nat := f 5

-- inductive Niche (k : Nat) where
--   | user : Nat → Niche k

inductive Niche (k : Nat) where
  | user : Nat → Niche k

def org1 : Niche 5 := Niche.user 5


-- organism-level niche incrementation:
def incniche (n: Niche k) : Niche (1 + k) :=
  match n with
  | Niche.user k => Niche.user (1 + k)

-- niche-level niche incrementation:

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
