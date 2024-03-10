import Mathlib.Data.Vector
-- import Mathlib.Data.Vector.Basic

/-
-- find an import to replace this:
inductive Vect (α  : Type u) : ℕ → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr
-/

-- Note the natural number type can be rep'ed either by Nat or ℕ.

inductive Niche : (k : ℕ) → Type where
  | user : (k : ℕ) → Niche k
deriving Repr

-- For this alternative syntax, see https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html
def incUser : (o : Niche k) → (Niche k.succ)
  | (Niche.user k) => Niche.user k.succ

-- Though the following works.  But note that it doesn't depend directly
-- on the existence of a Niche k. Otoh, if the niche user exists,
-- then the Niche exists.  (Note use of alternate syntax see above.)
def incOrg2niche : (o : Niche k) → Type
  | Niche.user k => Niche k.succ

-- dep pairs/Sigma types
-- https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html
--https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html?highlight=Sigma#what-makes-dependent-type-theory-dependent 

-- Note alternate syntaxes at the type and instance level:
def mkNichePair    (k : ℕ) : (_ : ℕ) × Type  := ⟨k, Niche k⟩
def mkNichePairAlt (k : ℕ) : (Σ _ : ℕ, Type) := Sigma.mk k (Niche k)

#check mkNichePair
#check (mkNichePair)

def np0 : (_ : ℕ) × Type := mkNichePair 0

#check np0
-- #eval np0

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
instance : CoeSort (Σ _ : ℕ, Type) Type where
  coe p := p.snd
-- alt syntax: instance : CoeSort (k : ℕ) × Type Type
  
-- Regular version of defining a niche user:
def u1 : Niche 1 := Niche.user 1
#check u1
#eval u1

-- We can define a type sig using the dep pair:
def u2 : (mkNichePair 2).snd := Niche.user 2
#check u2
#eval u2

-- And the CoeSort statement allows us to do it without using .snd.
-- WAIT IS THIS WHAT I WANTED TO DO?  DON'T I WANT THE ST TO BE AN INSTANCE OF ITS SECOND ELEMENT?
def u3 : (mkNichePair 3) := Niche.user 3
#check u3
#eval u3

-- Predefining a niche pair type (Is it bad or good form to initial-cap it?:
def Niche4 : (Σ _ : ℕ, Type) := mkNichePair 4
def u4 : Niche4 := Niche.user 4
#check u4
#eval u4

#check Niche4

-- So now the dependent pair containing the Niche can function
-- as a type of an organism.  But it also contains the information
-- that allows us to extract its parameter (index).

-- Version using .fst:
def incNicheOK (p : (Σ _ : ℕ, Type)) : (Σ _ : ℕ, Type) :=
  let k := p.fst
  Sigma.mk k.succ (Niche k.succ)

-- Version using pattern matching on the dependent pair:
def incNiche : (p : (Σ _ : ℕ, Type)) → (Σ _ : ℕ, Type)
  | ⟨k, _⟩ => ⟨k.succ, Niche k.succ⟩  -- Those are angle brackets.

#eval Niche4.fst
#eval (incNiche Niche4).fst
#check incNiche Niche4
#eval (incNiche (incNiche Niche4)).fst

def Niche6 : (Σ _ : ℕ, Type) := (incNiche (incNiche Niche4))
def u6 : Niche6 := Niche.user 6
#check u6
#eval u6

def niches := [Niche4, Niche6]
#check niches

#check List.map incNiche niches

-- What these are returning is not a list, but a function
-- from a proof the list is not empty, to the head.
#check (List.map incNiche niches).head
#check List.head (List.map incNiche niches)
-- #eval nichevect

def yo := Vector.cons 2 <| Vector.cons 4 Vector.nil
#check yo
#eval yo
#eval Vector.map (. + 1) yo

def nichevect := Vector.cons Niche4 <| Vector.cons Niche6 Vector.nil
#check nichevect
#check Vector.map incNiche nichevect
-- #eval Vector.map incNiche nichevect



-- Taking stock:
--
-- Given a niche user (an organism), incUser creates a user with parameter that
-- is one greater than the original user's parameter.
-- 
-- The type of a niche user is, strictly speaking, a Niche k, but via
-- coercion, a dependent pair of a parameter k and Niche k can function
-- as the type of a user.  
--
-- Moreover, that kind of pair type can be used by incNiche to
-- create a new niche pair that has parameter that is one larger.
--
-- I can make a list of such "niches".
--
-- I don't yet know how to map over a collection of niches in Lean.
