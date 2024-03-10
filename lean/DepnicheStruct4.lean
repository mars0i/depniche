
inductive Niche : (k : Nat) -> Type where
  | user : (k : Nat) -> Niche k
  deriving Repr

-- inspiration:
-- def mkNichePair (k : Nat) : (Σ _ : Nat, Type) := ⟨k, Niche k⟩

structure NicheUser (n : Nat) where
  k : Nat
  type : Type
  deriving Repr

def mkNicheUser (k : Nat) : NicheUser k := NicheUser.mk k (Niche k)

def nu4 := mkNicheUser 4
#check nu4
#eval nu4.k
#check nu4.k
#check nu4.type
-- #eval nu4.type

instance : CoeSort (NicheUser k) Type where
  coe nu := nu.type

-- Let's show that NicheUser k now also has is a Niche k by using it to
-- specify the type of a Niche.user k:
def u : (mkNicheUser 4) := Niche.user 4
#check u
#eval u

--
-- def incNiche (nu : NicheUser k) : NicheUser (k + 1) :=
--   mkNicheUser (nu.k + 1)

