-- Curious whether I can build the idea of a Sigma type into a custom
-- niche-related data structure.

/- The original:
from https://github.com/leanprover/lean4/blob/6fce8f7d5cd18a4419bca7fd51780c71c9b1cc5a/src/Init/Core.lean#L168-L176
structure Sigma {α : Type u} (β : α → Type v) where
  mk ::
  fst : α
  snd : β fst
-/

inductive Niche : (k : ℕ) → Type where
  | user : (k : ℕ) → Niche k
deriving Repr

def mkNicheType (k : Nat) : Type := Niche k

structure NichePair (mkNicheType : Nat → Type) where
  fst : Nat
  snd : mkNicheType fst

-- This works, but it shows that what I did above is not what I intended.
def np := NichePair.mk 3 (Niche.user 3)
#check np
#check np.fst
#check np.snd
#eval np.fst
#eval np.snd

