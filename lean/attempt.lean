-- Playing with Kyle Miller's suggestion

structure User where
  k : Nat
  deriving Repr

structure Niche (k : Nat) where
  n : Nat
  deriving Repr

/-- Creates an automatically-initialized field for each User instance. 
    It will contain a Niche type with dependent-index corresponding to
    User's k field.  Note that a Niche instance is not created, so
    there's no question about what value is in the n field. -/
def User.type (u : User) : Type := Niche u.k
/- This is called adding a variable in the namespace User, but does more.
   btw the following syntax doesn't work; u doesn't get bound in rhs:
       def User.type : (u : User) -> Type := Niche u.k
   I initially thought the syntaxes were equivalent; apparently not. -/

-- Make it automatic; turn a `User` into a type wherever it's used in a place expecting a type:
instance : CoeSort User Type := ⟨User.type⟩

-- organism-level niche incrementation: increment an organism's niche
def incNiche {k : Nat} (o : Niche k) : Niche (k + 1) :=
  -- Syntax to reuse the fields for the new type:
  {o with}

/-- Generate a new niche from an old niche, incrementing the index. -/
def incUser (n : User) : User  :=
  {k := n.k + 1}

def incNiche' (n : User) (o : n) : incUser n :=
  incNiche o

------------------------------
-- examples, tests

#check Niche
#check (Niche) -- Niche is fn from nat to type *because* its a dep type
               -- i.e. the fact that it has a field doesn't cause that.
#check (User)  -- User has a field but no dependent index, so not a fn
#check (Niche.mk) -- The constructors are fns though
#check (User.mk)

def u3 := User.mk 3
#check u3
#eval u3
def u4 := User.mk 4

#check (User.type)
#check u3.type
-- #eval u3.type

def n3 : Niche 3 := Niche.mk 3  -- need type sig to grab index
def n34 : Niche 3 := Niche.mk 4  -- this is poss but not what I want

def User.irrelevant (u : User) : String := s!"Onomotopeia {u.k}"
#eval u3.irrelevant
#eval u4.irrelevant
