import Mathlib

inductive Niche : (k : ℕ) → Type where
  | user : (k : ℕ) → Niche k
deriving Repr

def n := Niche 4
#check n

def u := Niche.user 4
#check u
#eval u

def Niche.type (_ : Niche k) : Type := Niche k
def Niche.alsotype : (Niche k) → Type := Niche

#check u.type
#check u.alsotype

-- sigs are same except for one var name:
#check Niche.type
#check Niche.alsotype

def Niche.fourtytwo : Nat := 42
#check Niche.fourtytwo
#eval Niche.fourtytwo
-- #check u.fourtytwo -- error. Why? Maybe only if it's a fn is it attached to the instance.


structure Nicz (typeidx : Nat) where
  instanceidx : Nat
  deriving Repr

-- External constructor that forces the type index and field to be the same:
def mkNicz (k : Nat) : Nicz k := Nicz.mk k
#check mkNicz
#check (mkNicz)
def ncz := mkNicz 5
#check ncz
#eval ncz
-- But you can still do this:
def nczbad : Nicz 5 := {ncz with instanceidx := 15}
-- or even:
def niczarefree : Nicz 42 := {ncz with instanceidx := 15}
-- So one must not do that.

-- I'm not even sure that you can prove that the the two indexes are the
-- same, given that there's no typecase, and the field value isn't 
-- represented in the type.
-- So it's a job for the universe pattern, I guess, but I'm sceptical
-- still.

