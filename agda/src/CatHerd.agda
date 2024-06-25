-- Marshall's temporary basic syntax and semantics experiments, MWE's etc.
module CatHerd where

open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Agda.Builtin.Sigma
open import Data.Product.Base using (_×_; _,′_) -- Needs stdlib 2.0

data Cat : ℕ → Set where
  cat : (id : ℕ) → Cat id

----------------------------------------

carly : Cat 0
carly = cat 0

carl : Cat 1
carl = cat 1

singleton-cat = carly ∷ []

herd-of-one-cat = (cat 0) ∷ singleton-cat

-- Fails because (Cat 1) and (Cat 2) are different types:
-- herd = carl ∷ singleton-cat
-- 0 != 1 of type ℕ when checking that the expression singleton-cat has type List (Cat 1)

-- But this works, as suggested by Naïm Camille Favier
-- https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Collection.20of.20indexed.20type.20with.20different.20indexes.3F/near/446454518:
herd : List (Σ ℕ Cat)
herd = (0 , carly) ∷ (1 , carl) ∷ []
-- The type signature is required.

----------------------

f : (x : ℕ) → (y : ℕ) → ℕ
f x y = x * y

-- The following type checks. Second line is what the holes guided me to.  wtf?
fpairs : Σ ℕ (λ x → (Σ ℕ (λ y → ℕ)))
fpairs = 2 , (3 , 2 * 3) -- where are the functions?  If you η-abstract, it's an erro.

-- This pair type is the analogue of simple pair tuples in Haskell or Idris.
-- It's defined in terms of Σ pairs, so fst and snd work on it.
foo : (Cat 3) × ℕ
foo = cat 3 ,′ 42

----------------------
-- Here's a way to use dependent pairs to make a list of double-index datatypes.
-- Lots of other things didn't work.

data Fish : ℕ → ℕ → Set where
  fish : (id : ℕ) → (color : ℕ) → Fish id color

fishpairer : ℕ  → ℕ  → Σ ℕ (λ id → (Σ ℕ (λ color → Fish id color)))
fishpairer id color = id , color , fish id color

school : List (Σ ℕ (λ id → (Σ ℕ (λ color → Fish id color))))
school = (fishpairer 0 1) ∷ (fishpairer 1 5) ∷ []

-- Explanation:
-- I was thinking that the second element of a dep pair is supposed
-- to be a function.  But it's not; it's a function application.
-- Aparently a pair is already that.  And 
-- You need to do something like defining fishpairer so that you can
-- bind the parameters of the function to the earlier pair elements.
-- Something like that.

----------------------
data Dog {id : ℕ} : Set where
  dog : Dog

donna : Dog {id = 0}
donna = dog

dan : Dog {id = 1}
dan = dog

singleton-dog = donna ∷ []

pack-of-donnas = donna ∷ singleton-dog

donny : Dog {id = 0}
donny = dog

donny-and-donna = dog ∷ donny ∷ singleton-dog

dan-pack = dog ∷ dan ∷ []
dan-and-donna = dog ∷ dan ∷ []

dogs : List (Dog {id = 0})
dogs = dog ∷ dog ∷ []

-- Fails for a similar reason, I guess:
-- pack = dan ∷ singleton-dog
-- error: 0 !=< 1 of type ℕ when checking that the expression singleton-dog has type List Dog

-- And this works, again per Favier's suggestion:
pack : List (Σ ℕ (λ i → (Dog {id = i}))) -- η-abstraction for the implicit index
pack = (0 , donna) ∷ (1 , dan) ∷ []

---------------------------

data Turtle : ℕ → ℕ → ℕ → Set where
  turtle : (id : ℕ) → (env : ℕ) → (speed : ℕ) → Turtle id env speed

tuple-to-turtle : (tuple : Σ ℕ (λ _ → (Σ ℕ (λ _ → ℕ)))) → Set
tuple-to-turtle = λ tuple → Turtle (fst tuple) (fst (snd tuple)) (snd (snd tuple))

TurtleTuple : Set
TurtleTuple = Σ (ℕ × ℕ × ℕ) tuple-to-turtle

tuple-turtle : ℕ → ℕ → ℕ → TurtleTuple
tuple-turtle id env speed = (id ,′ env ,′ speed) , turtle id env speed

{-
(λ tuple → let id : ℕ
                                 id = fst tuple
                                 env : ℕ
                                 env = fst (snd tuple)
                                 speed : ℕ
                                 speed = snd (snd tuple)
                             in (Turtle id env speed))
-}
