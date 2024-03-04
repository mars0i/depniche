
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

-- Though this works.  But note that it doesn't depend directly
-- on the existence of a Niche k. Otoh, if the niche user exists,
-- then the Niche must exist.  (Note use of alternate syntax see above.)
def org2niche : (o : Niche k) → Type
  | Niche.user k => Niche k.succ

#check org2niche
#check (org2niche)

def osNewNiche := org2niche o
#check osNewNiche
-- #eval osNewNiche




-- btw I never got this syntax working:
-- inductive Niche (k : Nat) : Type where
-- It turns out that copying Idris and Agda as closely as possible
-- makes it work as I intend.
