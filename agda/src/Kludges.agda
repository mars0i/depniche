module Kludges where

open import Data.List
open import Data.Nat

exploding-head : {A : Set} → A → List A → A
exploding-head default [] = default
exploding-head _ (x ∷ xs) = x

stuff = 1 ∷ 2 ∷ 3 ∷ []

thing = exploding-head 10000000 stuff
thang = exploding-head 10000000 []
