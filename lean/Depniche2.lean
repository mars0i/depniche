-- btw I never got this syntax working:
-- inductive Niche (k : Nat) : Type where
-- It turns out that copying Idris and Agda as closely as possible
-- makes it work as I intend.

-- @[match_pattern] -- added because of error message on inNiche, but don't understand

inductive Niche : (k : Nat) → Type where
  | user : (k : Nat) → Niche k
deriving Repr

#check Niche
#check (Niche)
#check Niche 5
#check (Niche 5)

def o : Niche 5 := Niche.user 5
#check o
#eval o

def o' := Niche.user 5
#check o'
#eval o'


-- For this alternative syntax, see https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html
def incOrganism : (o : Niche k) → (Niche k.succ)
  | (Niche.user k) => Niche.user k.succ


def oplus : (Niche 6) := incOrganism o
#check oplus
#eval oplus


def incNicheSilly (n : Type) (k : Nat) : Type :=
  Niche k.succ
  
 -- As I was told in the Zulip chat, this won't work:
/--
def incNiche {k : Nat} (n : Type) : Type :=
  match n with
  | (Niche k) => Niche k.succ
--/

-- Though the following works.  But note that it doesn't depend directly
-- on the existence of a Niche k. Otoh, if the niche user exists,
-- then the Niche exists.  (Note use of alternate syntax see above.)
def org2niche : (o : Niche k) → Type
  | Niche.user k => Niche k.succ

#check org2niche
#check (org2niche)

def osNewNiche : Type := org2niche o
#check osNewNiche
-- #eval osNewNiche


-- What's needed to modify a Niche is to get access to its parameter(s),
-- i.e. index(es).  What if we use dependent pairs?
-- No, Lean doesn't like this:

-- def nichepair (k : Nat) : ⟨Nat, fun n => Type⟩ := Sigma.mk k (fun k => Niche k)

-- Note a dep pair *type* can be rep'ed either with the cross product
-- syntax in the next line, or as something like (Σ k : Nat, Type).

-- Got it!
def mkNichePair (k : Nat) : (k : Nat) × Type := ⟨k, Niche k⟩
#check mkNichePair
#check (mkNichePair)

-- These s/b equivalent--just different syntax.
def np0 : (Σ k : Nat, Type)  := mkNichePair 0
-- def np0 : (k : Nat) × Type := mkNichePair 0

#check np0
-- #eval np0
-- I think the error on this last line just says that it doesn't know how to display
-- it.  Adding "deriving Repr" doesn't help--it doesn't know how to do that
-- automatically with Repr.

#check np0.1
#eval np0.1
#check np0.2
-- #eval np0.2  -- doesn't know how to display this

-- NOW I could maybe do one of those CoeSort aliases to
-- use the dep pair as if it was a Niche.  Which would be cool.
  
