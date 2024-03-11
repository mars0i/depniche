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
  {o with}   -- i.e. copies all vals of fields, without replacing any


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


#check incUser u3
#eval incUser u3 -- works--increments user's k field

#check incNiche
#check (incNiche)

-- This shows that incNiche generate *an instance of the type (Niche 4):
#check incNiche n3
-- This shows that it is an instance. The n field is copied, not inc'ed:
#eval incNiche n3
-- NOTE that this is not what I wanted: It's creating an instance of
-- the type Niche 4, and not the type itself.

#check incNiche' u3
#check incNiche' u3 _  -- The hole has type: User.type u3

-- These don't work:
#check incNiche' u3 u3
#check incNiche' u3 u3.type   -- this and next one mean the same thing
#check incNiche' u3 (User.type u3)
#check incNiche' u3 User.type 
#check incNiche' u3 (Niche 3)

-- This one type checks!
-- I think it's creating an instance of the Niche j type, where
-- j is the arg to Niche.mk.
#check incNiche' u3 (Niche.mk 3)
#eval incNiche' u3 (Niche.mk 15)
-- NOTE again this is not what I wanted: It's creating an instance of
-- the type Niche 15, and not the type itself.

