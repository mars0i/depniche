-- Kludgey functions, etc. to ease testing and experiments

module Kludges where

open import Data.List
-- open import Data.Nat

exploding-head : {A : Set} → A → List A → A
exploding-head default [] = default
exploding-head _ (x ∷ _) = x

exploding-tail : {A : Set} → A → List A → List A
exploding-tail default [] = [ default ]
exploding-tail _ (_ ∷ xs) = xs

{- Tests
stuff = 1 ∷ 2 ∷ 3 ∷ []
thing = exploding-head 10000000 stuff
whatever = exploding-head 10000000 []
less-stuff = exploding-tail 10000000 stuff
whatever2 = exploding-tail 10000000 []
-}
