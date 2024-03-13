
-- We can create ordered pairs either using parentheses or angle brackets:
def pair1 : Nat × String := (1, "2")
def pair2 : Nat × String := ⟨1, "2"⟩ 
#check pair1
#check pair2
#eval pair1
#eval pair2

-- def badpair1 : Nat × String := Sigma.mk 1 "2"

def pair3 : (Σ n : Nat, String) := ⟨1, "2"⟩
#check pair3
#eval pair3
-- def pair4 : (Σ n : Nat, String) := (1, "2") -- but you can't use parentheses for Sigma types.

-- Merely adding/removing a name for the instance of the first type changes the type.
def pair4 : (k : Nat) × String := ⟨1, "2"⟩
#check pair4
#eval pair4
-- That's a potential source of bugs, and is a reason to avoid using angle brackets rather than Sigma.mk.
-- Otoh the subtle differences in notation are built into how these types and values are reported,
-- and using the cross and angle brackets vs. parens reflects those representations.
