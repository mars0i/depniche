module CatHerd where

open import Data.List
open import Data.Nat
open import Agda.Builtin.Sigma

data Cat : ℕ → Set where
  cat : (id : ℕ) → Cat id

carly : Cat 0
carly = cat 0

carl : Cat 1
carl = cat 1

singleton-cat = carly ∷ []

herd-of-one-cat = (cat 0) ∷ singleton-cat

-- Fails because (Cat 1) and (Cat 2) are different types:
-- herd = carl ∷ singleton-cat
{- error:
0 != 1 of type ℕ
when checking that the expression singleton-cat has type List (Cat 1)
-}


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
{- error:
0 !=< 1 of type ℕ
when checking that the expression singleton-dog has type List Dog
-}




