import Mathlib.Data.Vector  -- used in examples near end

/-! 
What is in this file?

Niches as types, niche users as organisms or aspects of organisms
that have those types.

Indexed types allow niche construction, i.e. modification of a
niche by an organism (as well as environmental change -- for
other reasons).

For the sake of illustration, the indexes/parameters of Niches
(and their users) are Nats, and the only kind of niche
construction is incrementing a Nat.

Lean doesn't have "typecase": If you define an "inductive" type
(the `inductive` keyword does more or less what `data` does in
Idris or Agda, i.e. a dependent type extension of Haskell's
`data`) in Lean, you can pattern match on the contructors, but
you can't pattern match on the type itself. (Agda [and Coq?] have
the same restriction this, while Idris allows matching on the
type itself.)  That means that you can't read the index of an
indexed type from a type in order to create a new type with a
different index based on the old one.  If you want the index, you
have to get it somewhere else.

One place you can get the index is from an instance of the type
(since you can pattern match on constructors).  This is illustrated
by incOrgToNiche below.  However, a niche user should not have the power to
create a niche from scratch, so getting a niche parameter from a niche user
only makes sense if the niche user only exists if its niche type exists.
(I guess I need to think about what existence means here.)

The code below defines a dependent pairs/Sigma types as wrappers
for Niche types, so that the type index can be stored outside of
the type.  Then we use Lean's CoeSort to coerce the dependent
pairs to be Niche types, so that they can be used as if they were
the types of niche users.  (It should also be possible to do
something like this using Lean structures.  See
DepnicheKyleMiller.lean and other exploratory files here.)

(Perhaps it's silly to create a data structure to hold an index because
you are unable to access it from the type itself, and then call
the data structure the type.  But this file shows one way that it can be
done.)

-/

/- Tips to myself:

Note the natural number type can be rep'ed either by Nat or ℕ (ℕ).
And you can use either → (→) or -> for function definitions.

For the less common, more Haskell-ey function type syntax used
sometimes below (which is not what you usually see in introductory
examples), see
https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html

Information about dependent pairs/Sigma types:
https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html
https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html?highlight=Sigma#what-makes-dependent-type-theory-dependent 

Information CoeSort:
https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html?highlight=CoeSort#coercing-to-types
https://lean-lang.org/theorem_proving_in_lean4/type_classes.html?highlight=CoeSort#coercions-using-type-classes
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Construct.20type.20from.20index.20in.20another.20type/near/423694347
-/

inductive Niche : (k : ℕ) → Type where
  | user : (k : ℕ) → Niche k
deriving Repr

/-- Create a new niche user. -/
def incUser : (o : Niche k) → (Niche k.succ)
  | (Niche.user k) => Niche.user k.succ

/-- Create a new niche type by incrementing the index of a niche user. -/
def incOrgToniche : (o : Niche k) → Type
  | Niche.user k => Niche k.succ

/- Functions to create Sigma type wrappers of niche types.  

The functions immediately below are the same but illustrate the
different syntaxes for Sigma types. I may use all or most of
these syntaxes, unsystematically, below. You can mix and match
the different syntaxes.  The underscore Nat really is used, to
creates something whose type is Type, so it seems to be ignored
at the type level.  Using underscore rather than a properly named
variable gets rid of unused-variable warnings.

-/
def mkNichePairCrossAngle    (k : ℕ) : (_ : ℕ) × Type  := ⟨k, Niche k⟩
def mkNichePairSigmaMk (k : ℕ) : (Σ _ : ℕ, Type) := Sigma.mk k (Niche k)
def mkNichePairNoUnicode (k : Nat) : (Sigma (fun _ : Nat => Type)) := Sigma.mk k (Niche k)
def mkNichePair := mkNichePairNoUnicode -- chose one of the functions

-- We can define an abbreviation for that Sigma type, though it doesn't
-- work to use it with CoeSort, apparently.
def NicheWrapper := (Σ _ : ℕ, Type)

/-- Define a coercion so that the Sigma type wrapper of a niche type can
    function as a niche type. -/
instance : CoeSort (Σ _ : ℕ, Type) Type where
  coe p := p.snd

-- So now the dependent pair containing the Niche can function
-- as a type of an organism.  But it also contains the information
-- that allows us to extract its parameter/index.

/-- Increment a niche type itself (actually a Sigma type wrapper). 
    This version uses pattern matching on the dependent pair, but you could
    also extract the index using the fst function -/
def incNiche : (p : (Σ _ : ℕ, Type)) → (Σ _ : ℕ, Type)
  | ⟨k, _⟩ => ⟨k.succ, Niche k.succ⟩  -- Those are angle brackets.

---------------------------------------------------
-- Tests and illustrations

-- Basic illustrations of the niche and user data structures:

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
-- As specified in the sig of np0, snd has type Type, so there's no further
-- information about how to display it.
  
-- Regular version of defining a niche user:
def u1 : Niche 1 := Niche.user 1
#check u1
#eval u1

-- We can define a type signature by extracting it from the wrapper:
def u2 : (mkNichePair 2).snd := Niche.user 2
#check u2
#eval u2

-- And the CoeSort statement allows us to do the same thing without using .snd.
def u3 : (mkNichePair 3) := Niche.user 3
#check u3
#eval u3

-- Predefining a niche pair type, and then using that in a type signature:
def Niche4 : (Σ _ : ℕ, Type) := mkNichePair 4
def u4 : Niche4 := Niche.user 4
#check u4
#eval u4

#check Niche4
#eval Niche4.fst

-- Try out the incNiche function:

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

-- Using Vectors:

def nichevect := Vector.cons Niche4 $ Vector.cons Niche6 Vector.nil  -- It's better style to use <| rather than $ .
#check nichevect
#check Vector.map incNiche nichevect
-- #eval Vector.map incNiche nichevect -- Lean doesn't know how to display this.
#eval Vector.map (fun p => p.fst) $ Vector.map incNiche nichevect

