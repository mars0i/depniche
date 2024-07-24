{-# OPTIONS --cubical-compatible --safe #-}

module learning/CatMap where

import Data.Tree.AVL.Map as M

-- This module is parametrised by keys, which have to form a (strict)
-- total order, and values, which are indexed by keys. Let us use
-- natural numbers as keys and vectors of strings as values.

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base as Prod using (_,_; _,′_; _×_)
open import Data.Maybe.Base as Maybe using (Maybe)
open import Data.String.Base using (String)
open import Data.Vec.Base using (Vec; _∷_; [])
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- open Data.Tree.AVL <-strictTotalOrder 
open M <-strictTotalOrder

-----------------------------------
--- Nat values and keys

empty-sign-map : Map ℕ
empty-sign-map = empty

singleton-sign-map : Map ℕ
singleton-sign-map = singleton 0 0

doubleton-sign-map : Map ℕ
doubleton-sign-map = insert 1 1 singleton-sign-map

three-sign-map : Map ℕ
three-sign-map = insert 2 0 doubleton-sign-map

sign-map : Map ℕ
sign-map = insert 3 1 three-sign-map

twoIsInIt : Bool
twoIsInIt = member 2 sign-map

fourIsnt : Bool
fourIsnt = member 4 sign-map

maybe-three : Maybe ℕ
maybe-three = lookup sign-map 3

maybe-two : Maybe ℕ
maybe-two = lookup sign-map 2

sign-list : List (ℕ × ℕ)
sign-list = toList sign-map

next-sign-list : List (ℕ × ℕ)
next-sign-list = (4 , 0) List.∷ (5 , 1) List.∷ List.[]

next-sign-map : Map ℕ
next-sign-map = fromList next-sign-list

more-sign-map : Map ℕ
more-sign-map = union sign-map next-sign-map

maybe-two' : Maybe ℕ
maybe-two' = lookup more-sign-map 2

maybe-four : Maybe ℕ
maybe-four = lookup more-sign-map 4


--------------------------------
-- String values, Nat keys

empty-natstring-map : Map String
empty-natstring-map = empty

natstring-map : Map String
natstring-map = fromList ((0 , "Zero")List.∷
                          (1 , "One") List.∷
                          (5 , "Five") List.∷
                          (3 , "Three") List.∷
                          List.[])

natstring-list = toList natstring-map

just-five = lookup natstring-map 5
nothing-four = lookup natstring-map 4







