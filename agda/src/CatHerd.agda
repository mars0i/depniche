module CatHerd where

open import Data.List
open import Data.Nat using (ℕ) -- ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base using (_×_; _,′_)
open import Function.Base using (_∘_)
open import Agda.Builtin.Sigma

{-
   Examples illustrating using dependent and non-dependent pairs to
   bundle up elements of indexed so that they can be stored in lists.
   The problem is that indexed types are different types when they have
   different indexes, elements with different indexes can't be directly
   stored in a list.
-}

--------------------------------

data Mouse : ℕ → Set where
  mouse : (id : ℕ) → Mouse id

make-mouse-pair : ℕ → Σ ℕ Mouse
make-mouse-pair id = id , mouse id

remy-pair = make-mouse-pair 3
remy = snd remy-pair

nest = make-mouse-pair 1 ∷ make-mouse-pair 2 ∷ []

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

felix-pair = make-cat-pair 3 5
felix = snd felix-pair

herd = make-cat-pair 1 5 ∷ make-cat-pair 2 7 ∷ []

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

lassie-pair = make-dog-pair 3 5 7
lassie = snd lassie-pair

pack = make-dog-pair 1 5 6 ∷ make-dog-pair 2 4 2 ∷ []

-- fst-of-snd : {A B C : Set} → Σ A (Σ B C) → B
-- fst-of-snd x = fst (snd x)
