-- Kinds of structure definitions 

----------------------------------------------
-- Type parameters can only be added via a type signature, and
-- it is required.

structure OnlyImplicit (k : Nat) where
  deriving Repr

#check OnlyImplicit.mk
#check (OnlyImplicit.mk)
-- def oi3no := OnlyImplicit.mk -- "don't know how to synthesize implicit argument"
def oi3 : OnlyImplicit 3 := OnlyImplicit.mk
#check oi3
#eval oi3


----------------------------------------------
-- If you also have a field, it's still the case that 
-- type parameters can only be added via a type signature
-- and it is required.

structure ImplicitPlusField (k : Nat) where
  k : Nat
  deriving Repr

#check ImplicitPlusField.mk
#check (ImplicitPlusField.mk)
-- def ipf3no := ImplicitPlusField.mk 3 -- "don't know how to synthesize implicit argument"
def ipf3 : ImplicitPlusField 3 := ImplicitPlusField.mk 3
#check ipf3
#eval ipf3

-- Note that there is nothing above that keeps the field and the type param
-- in sync:

def oiDiffParams : ImplicitPlusField 3 := ImplicitPlusField.mk 4
#check oiDiffParams
#eval oiDiffParams

-- This shows an advantage of using dependent pair instead, since
-- the accessible (left) parameter is required to be in sync with the
-- (right) type.  Of course it's possible to build in the constraint,
-- but this is already built in to the dependent pair.  (Of course
-- dependent pairs feel more raw and low-level.)

----------------------------------------------
-- If there is no type parameter, you can get away with not adding
-- a type signature; Lean will guess it.

structure OnlyField where
  k : Nat
  deriving Repr

#check OnlyField.mk
#check (OnlyField.mk)
def of3ok := OnlyField.mk 3
#check of3ok
#eval of3ok
def of3 : OnlyField := OnlyField.mk 3
#check of3
#eval of3

----------------------------------------------

-- If you create more fields, then the .mk constructor expects more
-- aguments.

structure MoreFields where
  k : Nat
  s: String
  deriving Repr

#check MoreFields.mk
#check (MoreFields.mk)

def mf3 := MoreFields.mk 3 "three"
#check mf3
#eval mf3
