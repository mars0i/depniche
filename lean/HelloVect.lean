-- For reference: the canonical dependent type example in Lean (from FPIL I think)

inductive Vect (α  : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr
-- Note that the Nat arg is defined inductively.  It's not ever
-- passed explicitly in the def of Vect.  otoh the def of cons
-- does include a nat int it.  That is at the type level, though.

-- example is a keyword
example : (Vect String 0)  := Vect.nil
example : Vect String 2 := Vect.cons "a" (Vect.cons "b" Vect.nil)

def vs : Vect String 2 := Vect.cons "a" (Vect.cons "b" Vect.nil)
#check vs
#eval vs

