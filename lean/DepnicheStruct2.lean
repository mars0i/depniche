
inductive Niche : (k : Nat) → Type where
  | user : (k : Nat) → Niche k
  deriving Repr

structure NicheUser (k : Nat) where  -- not the same k as below
  k : Nat
  typeUser : Type
  deriving Repr

-- instance : CoeSort (NicheUser k) (Niche k) where
instance : CoeSort (NicheUser k) Type where
  coe nu := nu.typeUser

def nu3 : NicheUser 3 := NicheUser.mk 3 (Niche 3)
def nu3' : Niche 3 := NicheUser.mk 3 (Niche 3)
-- def nun3 : Niche 3 := nu3

-------------------------------------------
-- Illustrations and clarifications

#check Niche.user
#check (Niche.user)
#check Niche.user 3
#eval Niche.user 3

#check NicheUser.mk
#check (NicheUser.mk)

-- The definition of NicheUser constrains the type to have the same index:
-- def nuOops := NicheUser.mk 3 (Niche.user 4)  -- application type mismatch

/-
-- old version
def nu3 := NicheUser.mk 3 (Niche.user 3)
#check nu3
#eval nu3
#check nu3.typeUser
#eval nu3.typeUser
#eval nu3.k
-/


