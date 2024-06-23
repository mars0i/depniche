-- Marshall's temporary basic syntax and semantics experiments, MWE's etc.
module CatHerd where

open import Data.List
open import Data.Nat
open import Agda.Builtin.Sigma

data Cat : ℕ → Set where
  cat : (id : ℕ) → Cat id

----------------------------------------
-- Just making sure I understand syntax options.
f : (x : ℕ) → (y : ℕ) → ℕ
f = λ x y → x * y

-- triple : Σ ℕ (λ x → (Σ ℕ (λ y → (f x y))))
-- triple = (2 , (λ x → (3 , (λ x y → x + y))))

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

