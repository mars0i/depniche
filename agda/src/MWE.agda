module MWE where

open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Product.Base
open import Function.Base
open import Agda.Builtin.Sigma

data Mouse : ℕ → Set where
  mouse : (id : ℕ) → Mouse id

mouse-sigma : ℕ → Σ ℕ Mouse
mouse-sigma id = id , mouse id

mice = mouse-sigma 1 ∷ mouse-sigma 2 ∷ []

data Cat : ℕ → ℕ → Set where
  cat : (id : ℕ) → (purr : ℕ) → Cat id purr

cat-sigma : ℕ → ℕ → Σ (ℕ × ℕ) (Σ[ v ∈ ℕ ] ℕ → Set)
cat-sigma id purr = ? -- (id ,′ purr) , (
