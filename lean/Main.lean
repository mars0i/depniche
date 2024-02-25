import «Depniche»

def yo : String := " this"

def f (x : Nat) : Nat := x + 1

def f5 : Nat := f 5

#eval yo
#eval f5
#check f

#check Type
#check Type 1

-- inductive Niche (i : Nat) : Type 1 where
--   | niche : Niche i

inductive Niche : (i : Nat) -> Type 1 where
  | niche : Niche i
deriving Repr

#check Niche
#check Niche 5
#check Niche.niche

def aniche : Niche 5 := Niche.niche
#check aniche
#eval aniche

def nutherniche : Niche 2 := Niche.niche
#check nutherniche
#eval nutherniche

-- def incniche (n: Niche i) : Niche (1 + i) :=
--   match n with
--   | (Niche i) => niche (1 + i)

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
