inductive Vect (α  : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

-- note example is a keyword
example : (Vect String 0)  := Vect.nil

example : Vect String 2 := Vect.cons "a" (Vect.cons "b" Vect.nil)

def vs : Vect String 2 := Vect.cons "a" (Vect.cons "b" Vect.nil)
#check vs
#eval vs

inductive Niche (α : Nat) : Type where
  | user : k → Niche k
deriving Repr
