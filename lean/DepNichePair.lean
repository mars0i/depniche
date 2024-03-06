

inductive Niche : (k : Nat) → Type where
  | user : (k : Nat) → Niche k
deriving Repr

-- For this alternative syntax, see https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html
def incOrganism : (o : Niche k) → (Niche k.succ)
  | (Niche.user k) => Niche.user k.succ

-- Though the following works.  But note that it doesn't depend directly
-- on the existence of a Niche k. Otoh, if the niche user exists,
-- then the Niche exists.  (Note use of alternate syntax see above.)
def org2niche : (o : Niche k) → Type
  | Niche.user k => Niche k.succ

-- dep pairs/Sigma types
-- https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html
--https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html?highlight=Sigma#what-makes-dependent-type-theory-dependent 

-- Note alternate syntaxes at the type and instance level:
def mkNichePair    (k : Nat) : (k : Nat) × Type  := ⟨k, Niche k⟩  -- Those are angle brackets made with \langle or \< , etc.
def mkNichePairAlt (k : Nat) : (Σ k : Nat, Type) := Sigma.mk k (Niche k)

#check mkNichePair
#check (mkNichePair)

def np0 : (k : Nat) × Type := mkNichePair 0

#check np0
-- #eval np0
-- I think the error on this last line just says that it doesn't know how to display
-- it.  Adding "deriving Repr" doesn't help--it doesn't know how to do that
-- automatically with Repr.

-- or .fst, .snd
#check np0.1
#eval np0.1
#eval np0.fst
#check np0.2
#check np0.snd
-- #eval np0.2  -- doesn't know how to display this

-- NOW I could maybe do one of those CoeSort aliases to
-- use the dep pair as if it was a Niche.  Which would be cool.

-- https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?highlight=CoeSort#coercing-to-types
-- https://lean-lang.org/theorem_proving_in_lean4/type_classes.html?highlight=CoeSort#coercions-using-type-classes
  
-- This is too general.  It's not constrained to Niches.
-- instance : CoeSort (k : Nat) × Type Type
instance : CoeSort (Σ k : Nat, Type) Type where
  coe p := p.snd

  

