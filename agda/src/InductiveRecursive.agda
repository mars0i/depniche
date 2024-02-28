-- from https://wiki.portal.chalmers.se/agda/ReferenceManual/Data

{-
... consider a type MyList of lists of natural numbers, with
the property that each list element is greater than the sum of
all list elements to its right. The constructor cons takes
three arguments: the head of the list n, the tail of the list
ns, and a proof that n > sum ns.
-}

module InductiveRecursive where

open import Data.Nat

data MyList : Set
sum : MyList -> ℕ

data MyList where
  nil : MyList
  cons : (n : ℕ) -> (ns : MyList) -> (n > sum ns) -> MyList

sum nil = zero
sum (cons n ns _) = n + sum ns


-------------------------------
-- examples

ml0 : MyList
ml0 = nil

ml1 : MyList
ml1 = cons 2 ml0 {!!}


