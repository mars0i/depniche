-- Marshall's lessons and experiments.
-- A collection of cats is a ... herd.
-- (And sometimes trying to get Agda to do what I want seems like herding cats.)
module learning/CatHerd where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat -- defines _==_ i.e. regular equality
open import Agda.Builtin.Sigma
open import Data.Bool -- has if/then as well as 𝔹

open import Data.List
-- no open, to avoid conflicts with List
import Data.Vec as V -- using (_∷_; [])

open import Data.Nat using (ℕ ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base using (_×_; _,′_)
open import Function.Base using (_∘_)

open import Kludges

{-
   Examples illustrating using dependent and non-dependent pairs to
   bundle up elements of indexed so that they can be stored in lists.
   The problem is that indexed types are different types when they have
   different indexes, elements with different indexes can't be directly
   stored in a list.
-}

-----------------------------------
-- Storing data in a data type without indexing

data Thing : Set where
  thing : (a : ℕ) → Thing
  thang : (a : ℕ) → (b : ℕ) → Thing

things : List Thing
things = thing 1 ∷ thing 25 ∷ thang 15 5 ∷ thing 4 ∷ thang 1 2 ∷ []

a-of-thing : Thing → ℕ
a-of-thing (thing a) = a
a-of-thing (thang a b) = a

--------------------------------
-- Sigma pair and normal pair tips

{-
I'm finally starting to get clear on this.

The second element of a Sigma pair *type* is a function that constructs
a *type*, given an instance of (type which is) the first element
of the type.

(To create a non-dependent pair by hand, just let the function that
is the second element ignore its argument.
Or abbreviate that process using × .)

The second element of the *instance* of a Sigma pair is any value
that has the type constructed in the Sigma type.  No function has
to be involved.
-}

-- Examples:

-- Non-dependent pair, since x is ignored in first line:
p : Σ ℕ (λ x → ℕ)
p = 2 , 5 * ((λ x → x + 2) 2)  -- second elem need not include any function: it just has to eval to a ℕ

-- Another non-dependent pair:
y : Σ ℕ (λ x → ℕ)
y = 2 , 3

-- Full-fledged dependent pairs:

-- If second arg of instance is not a ℕ, it won't type check:
q : Σ ℕ (λ x → if (x == 0) then ℕ else Bool)
q = 0 , 43

-- If second arg of instance is not a Bool, it won't type check:
r : Σ ℕ (λ x → if (x == 0) then ℕ else Bool)
r = 17 , false


{- This is why Sigma pairs are useful for indexed types, as
suggested by Naïm Camille Favier https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/.E2.9C.94.20Collection.20of.20indexed.20type.20with.20different.20indexes.3F/near/446454518

Each index gives you a different type, so it can't be used where you
need instances of the same type, as in a List. A Sigma pair in
which the second element of the type is an indexed type, is
something that is a single type, but that contains an instance of
a different type in the instance second, depending on the value
of the instance first.
-}


-- Another way of making a non-dep pair, avoiding verbosity of the
-- λ wrapper in the signature.
-- × and ,′ do the same thing, but add the λ wrapper for you.
-- And look--you can actually just use a comma instead of comma-tick
-- in this case.  Either one works.
x : ℕ × ℕ
x = 1 , 2


-- When I wrote these next two examples, I thought they were full-
-- fledged Sigma types, i.e. not non-dep pairs, but they're actually
-- non-dep pairs since the type returned by the snd in the signature
-- is constant.

-- You can pattern match on Sigma pairs
myfst : {A B : Set} → {a : A} → Σ A (λ x → B) → A
myfst (x , y) = x  -- the parens on lhs are required

mysnd : {A B : Set} → {a : A} → Σ A (λ x → B) → B  -- note type of result is different
mysnd (x , y) = y

-- And you can also pattern match with non-dep pairs,
-- but you have to use comma, not comma-tick.
myndfst : {A B : Set} → (A × B) → A
myndfst (a , b) = a

myndsnd : {A B : Set} →  (A × B) → B
myndsnd (a , b) = b

-- This works with iterated commas, too.
thd : {A B C : Set} → (A × B × C) → C
thd (a , b , c) = c

-- Pattern matching works with let, as I'd expect.
thd2 : {A B C : Set} → (A × B × C) → C
thd2 x = let (a , b , c) = x
         in c

-- SO WHAT'S THE DIFFERENCE BETWEEN COMMA AND COMMA-TICK?
-- I think it's this:
-- Sometimes it's possible to define a non-dependent pair
-- without a type signature.  In that case, you need comma-tick to tell
-- Agda what's going on with the second argument.  However, when you have
-- type signature using × then you can use either.  Not sure about that.


-- This shows that you can curry the Vec type to use it as the second
-- type in a Sigma pair.
spair : Σ ℕ (V.Vec ℕ)
spair = 3 , 1 V.∷ 2 V.∷ 5 V.∷ V.[]

-- However, if you want to make more than one Vec depend on the fst,
-- you need abstraction.
morepair : Σ ℕ (λ n → (V.Vec ℕ n) × (V.Vec ℕ n))
morepair = 2 , 1 V.∷ 2 V.∷ V.[] , 4 V.∷ 7 V.∷ V.[]
-- Note that because comma works for non-dep as well as dep pairs,
-- and it's right associative, a series of commas works in the second line.

--------------------------------

data Mouse : ℕ → Set where
  mouse : (id : ℕ) → Mouse id

make-mouse-pair : ℕ → Σ ℕ Mouse
make-mouse-pair id = id , mouse id

mouse-head = exploding-head (make-mouse-pair 1000)

remy-pair = make-mouse-pair 3
remy = snd remy-pair

nest = make-mouse-pair 1 ∷ make-mouse-pair 2 ∷ []

paulette = snd (mouse-head nest)

--------------------------------
-- Uses a non-dependent pair to store two arguments as the first
-- element of a dependent pair.  This is easier to work with
-- rather than iteratively embedding depent pairs in dependent pairs.

data Cat : ℕ → ℕ → Set where
  cat : (id : ℕ) → (purr : ℕ) → Cat id purr

-- Sigma type with non-dependent pair type as first element.
CatPair : Set
CatPair = Σ (ℕ × ℕ) (λ prod → Cat (fst prod) (snd prod))

-- Sigma type instance with non-dependent pair as first element.
-- Note comma-tick (non-dependent) vs. comma (dependent)
make-cat-pair : ℕ → ℕ → CatPair
make-cat-pair id purr = (id ,′ purr) , cat id purr


cat-head = exploding-head (make-cat-pair 1000 1000)

felix-pair = make-cat-pair 3 5
felix = snd felix-pair

herd = make-cat-pair 1 5 ∷ make-cat-pair 2 7 ∷ []

melissa = snd (cat-head herd)



--------------------------------
-- Shows how the non-dependent-pair-in-dependent pair can be
-- extended for more than two indexes.

data Dog : ℕ → ℕ → ℕ → Set where
  dog : (id : ℕ) → (bark : ℕ) → (size : ℕ) → Dog id bark size

-- Non-dependent pairs (like Sigma pairs) are right-associative, so
-- a pair with a pair in the second element looks like a triple.
DogPair : Set
DogPair = Σ (ℕ × ℕ × ℕ) (λ triple → Dog (fst triple)
                                        (fst (snd triple))
                                        (snd (snd triple)))

-- Non-dependent pairs (like Sigma pairs) are right-associative, so
-- a pair with a pair in the second element looks like a triple.
make-dog-pair : ℕ → ℕ → ℕ → DogPair
make-dog-pair id bark size = (id ,′ bark ,′ size) , dog id bark size

dog-head = exploding-head (make-dog-pair 1000 1000 1000)
dog-tail = exploding-tail (make-dog-pair 1000 1000 1000)

lassie-pair = make-dog-pair 3 5 7
lassie = snd lassie-pair

pack = make-dog-pair 1 5 6 ∷ make-dog-pair 2 4 2 ∷ []

geoffrey = snd (dog-head pack)
sara = snd (dog-head (dog-tail pack))
nobody = snd (dog-head (dog-tail (dog-tail pack)))

-- fst-of-snd : {A B C : Set} → Σ A (Σ B C) → B
-- fst-of-snd x = fst (snd x)

-----------------------------------------

-- Can Agda infer that the vecs must be equal without being told? Yes.
zipnats : {n : ℕ} → V.Vec ℕ n → V.Vec ℕ n → V.Vec (ℕ × ℕ) n
zipnats V.[] ws = V.[]
zipnats (v V.∷ vs) (w V.∷ ws) = (v ,′ w) V.∷ zipnats vs ws

v2 : V.Vec ℕ 2
v2 = 1 V.∷ 2 V.∷ V.[]
w2 : V.Vec ℕ 2
w2 = 10 V.∷ 20 V.∷ V.[]
x2 : V.Vec ℕ 3
x2 = 1 V.∷ 2 V.∷ 3 V.∷ V.[]

