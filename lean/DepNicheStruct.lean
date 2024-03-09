-- Attempt to use Kyle Miller's ideas in the way that I think
-- should have been intended.


structure Niche (k : Nat) where
  k : Nat
  deriving Repr

structure User where
  k : Nat
  deriving Repr

def User.type (u : User) : Type := Niche u.k

-- instance : CoeSort User (Niche k) := ⟨User.type⟩

def u5 := User.mk 5
#check u5
#eval u5

-- Seems not what I want
-- def u5 : (Niche 5) := User.mk 5
-- #check u5
-- #eval u5
