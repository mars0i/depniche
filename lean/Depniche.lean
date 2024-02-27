-- This module serves as the root of the `Depniche` library.
-- Import modules here that should be built as part of the library.
-- import «Depniche».Basic
-- import «Init».Prelude


@[match_pattern] -- added because of error message on inNiche, but don't understand
inductive Niche (k : Nat) where
  | organism : Nat → Niche k
deriving Repr


-- organism-level niche incrementation: increment an organism's niche
def incOrganism {k : Nat} (o : Niche k) : Niche k.succ :=
  match o with
  | Niche.organism k => Niche.organism k.succ -- why can't I use succ btw?

-- Kyle Miller says it can't work because you can't pattern match on types
-- because they're erased.
-- from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Construct.20type.20from.20index.20in.20another.20type/near/423694347
/-
/-- Generate a new niche from an old niche, incrementing the index. -/
def incNiche {k : Nat} (n : Type) : Type :=
  match n with
  | (Niche k) => Niche k.succ 
-/


#check Niche
#check (Niche 4)

-- attribute [match_pattern] Niche 
-- attribute [match_pattern] Niche k

-- Here is another idea.  I can't match on a type, but I can match
-- on an organism, and it gets to create the niche:
def org2niche {k : Nat} (o : Niche k) : Type :=
  match o with
  | Niche.organism k => Niche k.succ

#check org2niche (Niche.organism 5)
