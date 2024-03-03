inductive Niche (k : Nat) where
  | user : Nat -> Niche k
deriving Repr

#check Niche
#check Niche 5

def nu1 : Niche 5 := Niche.user 5
#check nu1
#eval nu1

-- Shows I don't understand inductive--I don't want this to work:
def nu2 : Niche 3 := Niche.user 5
#check nu2
#eval nu2
