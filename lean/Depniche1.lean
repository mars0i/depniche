--------------------
-- Standard example, using syntax from FPiL
inductive Vect (α  : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

-- note example is a keyword
example : (Vect String 0)  := Vect.nil

example : Vect String 2 := Vect.cons "a" (Vect.cons "b" Vect.nil)

#check Vect

/- Type error:
inductive Vect0 (α  : Type u) Nat : Type u where
  | nil : Vect0 α 0
  | cons : α → Vect0 α n → Vect0 α (n + 1)
deriving Repr
-/

-- Putting entire function type after the colon, Idris/Agda/Haskell-style:
inductive Vect1 : (α  : Type u) → Nat → Type u where
  | nil : Vect1 α 0
  | cons : α → Vect1 α n → Vect1 α (n + 1)
deriving Repr

#check Vect
#check Vect1

-- Using alternative function and match syntax:
def incnats : (Vect Nat k) → (Vect Nat k)
  | .nil => .nil
  | .cons n ns => .cons (n + 1) (incnats ns)   -- Lean matches succ on the right
  -- or: | .cons n ns => .cons (Nat.succ n) (incnats ns)

-- Eval fails without a type annotation to specify that it's a Nat vector (Idris/Agda/Haskell syntax is better)
#eval incnats (Vect.cons 2 (Vect.cons 3 Vect.nil) : Vect Nat 2)
#eval incnats (Vect.cons 2 (Vect.cons 3 (Vect.nil : Vect Nat 0)))

-- Original syntax
def incnats0 (xs : Vect Nat k) : (Vect Nat k) :=
  match xs with
  | .nil => .nil
  | .cons n ns => .cons (n + 1) (incnats ns)

def vs : Vect Nat 2 := Vect.cons 5 (Vect.cons 17 Vect.nil)
#check vs
#eval vs
#eval incnats vs
#eval incnats0 vs

#check incnats
#check incnats0
#check (incnats)
#check (incnats0)

--------------------
-- My experiments

/-
inductive Niche (α : Nat) : Type where
  | user : k → Niche k
deriving Repr
-/
