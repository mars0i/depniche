

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
-- #eval np0.2  -- doesn't know how to display this.
-- But Niche derives Repr.  So the problem is that it doesn't know it's a Niche k.
-- As specied in the sig of np0, snd has type Type, so there's no further
-- information about how to display it.
  

-- Now let's define a coercion so that a dep niche pair can function as a niche.

-- On CoeSort see:
-- https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?highlight=CoeSort#coercing-to-types
-- https://lean-lang.org/theorem_proving_in_lean4/type_classes.html?highlight=CoeSort#coercions-using-type-classes
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Construct.20type.20from.20index.20in.20another.20type/near/423694347

-- This def is too general.  It's not constrained to Niches.  But Type is the
-- type of (Niche k), so if you want to return a Niche k, the type is Type.
-- I suppose it could be constrained with a proof.
instance : CoeSort (Σ k : Nat, Type) Type where
  coe p := p.snd
-- alt syntax: instance : CoeSort (k : Nat) × Type Type
  
-- Regular version of defining a niche user:
def u1 : Niche 1 := Niche.user 1
#check u1
#eval u1

-- We can define a type sig using the dep pair:
def u2 : (mkNichePair 2).snd := Niche.user 2
#check u2
#eval u2

-- And the CoeSort statement allows us to do it without using .snd.
def u3 : (mkNichePair 3) := Niche.user 3
#check u3
#eval u3

-- Predefining a niche pair type (Is it bad or good form to initial-cap it?:
def Niche4 : (Σ k : Nat, Type) := mkNichePair 4
def u4 : Niche4 := Niche.user 4
#check u4
#eval u4

-- So now the dependent pair containing the Niche can function
-- as a type of an organism.  But it also contains the information
-- that allows us to extract its parameter (index).
