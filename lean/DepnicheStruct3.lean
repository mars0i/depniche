
inductive Niche : (k : ℕ) → Type where
  | user : (k : ℕ) → Niche k
deriving Repr

-- Supposed to play the role of a Sigma type in DepNichePair.lean
structure NicheUser where
  k : Nat       -- analogous to the fst
  type : Type   -- analogous to the snd
  deriving Repr

#check (NicheUser.mk)

def nu3 := NicheUser.mk 3 (Niche 3)
def nu3too : NicheUser := NicheUser.mk 3 (Niche 3)
#check nu3
#eval nu3
-- Note this allowed, but shouldn't be:
def nuOops := NicheUser.mk 3 Nat

-- Use this instead of NicheUser.mk to avoid that.
def mkNicheUser (k : Nat) : NicheUser := NicheUser.mk k (Niche k)

def nu3' := mkNicheUser 3
#check nu3'
#eval nu3'
#eval nu3'.k
-- #eval nu3'.type

instance : CoeSort NicheUser Type where
  coe u := u.type

-- Doesn't work.
-- def coerced : (Niche 3) := nu3'
