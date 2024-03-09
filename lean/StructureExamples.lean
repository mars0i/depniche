-- Kinds of structure definitions 

----------------------------------------------
-- Type parameters can only be added via a type signature, and
-- it is required.

structure NicheOnlyImplicit (k : Nat) where
  deriving Repr

#check NicheOnlyImplicit.mk
#check (NicheOnlyImplicit.mk)
-- def noi3no := NicheOnlyImplicit.mk -- "don't know how to synthesize implicit argument"
def noi3 : NicheOnlyImplicit 3 := NicheOnlyImplicit.mk
#check noi3
#eval noi3


----------------------------------------------
-- If you also have a field, it's still the case that 
-- type parameters can only be added via a type signature
-- and it is required.

structure NicheImplicitPlusField (k : Nat) where
  k : Nat
  deriving Repr

#check NicheImplicitPlusField.mk
#check (NicheImplicitPlusField.mk)
-- def nipf3no := NicheImplicitPlusField.mk 3 -- "don't know how to synthesize implicit argument"
def nipf3 : NicheImplicitPlusField 3 := NicheImplicitPlusField.mk 3
#check nipf3
#eval nipf3

-- Note that there is nothing above that keeps the field and the type param
-- in sync:

def noiDiffParams : NicheImplicitPlusField 3 := NicheImplicitPlusField.mk 4
#check noiDiffParams
#eval noiDiffParams

-- This shows an advantage of using dependent pair instead, since
-- the accessible (left) parameter is required to be in sync with the
-- (right) type.  Of course it's possible to build in the constraint,
-- but this is already built in to the dependent pair.  (Of course
-- dependent pairs feel more raw and low-level.)

----------------------------------------------
-- If there is no type parameter, you can get away with not adding
-- a type signature; Lean will guess it.

structure NicheOnlyField where
  k : Nat
  deriving Repr

#check NicheOnlyField.mk
#check (NicheOnlyField.mk)
def nof3ok := NicheOnlyField.mk 3
#check nof3ok
#eval nof3ok
def nof3 : NicheOnlyField := NicheOnlyField.mk 3
#check nof3
#eval nof3

----------------------------------------------

-- If you create more fields, then the .mk constructor expects more
-- aguments.

structure NicheMoreFields where
  k : Nat
  s: String
  deriving Repr

#check NicheMoreFields.mk
#check (NicheMoreFields.mk)

def nmf3 := NicheMoreFields.mk 3 "three"
#check nmf3
#eval nmf3
