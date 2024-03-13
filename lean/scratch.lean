

inductive Niche : (k : ℕ) → Type where
  | user : (k : ℕ) → Niche k
deriving Repr

def Niche.type (_ : Niche k) : Type := Niche k
def Niche.alsotype : (Niche k) → Type := Niche
def Niche.fourtytwo : Nat := 42

def n := Niche 4
#check n

def u := Niche.user 4
#check u
#eval u

#check u.type
#check u.alsotype
-- #check u.fourtytwo -- error. Why? Maybe only if it's a fn is it attached to the instance.

#check Niche.fourtytwo
#eval Niche.fourtytwo
-- sigs are same except for one var name:
#check Niche.type
#check Niche.alsotype
