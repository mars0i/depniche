-- Most of this is copied from
-- https://agda.github.io/agda-stdlib/v2.0/README.Data.Tree.AVL.html

{-# OPTIONS --cubical-compatible --safe #-}

module learning/CatMap where

-- import Data.Tree.AVL
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

empty-string-map : Map String
empty-string-map = empty





{-
StringsTree = Tree (MkValue (Vec String) (subst (Vec String)))

------------------------------------------------------------------------
-- Construction of trees

-- Some values.

v₁  = "cepa" ∷ []
v₁′ = "depa" ∷ []
v₂  = "apa" ∷ "bepa" ∷ []

-- Empty and singleton trees.

t₀ : StringsTree
t₀ = empty

t₁ : StringsTree
t₁ = singleton 2 v₂

-- Insertion of a key-value pair into a tree.

t₂ = insert 1 v₁ t₁

-- If you insert a key-value pair and the key already exists in the
-- tree, then the old value is thrown away.

t₂′ = insert 1 v₁′ t₂

-- Deletion of the mapping for a certain key.

t₃ = delete 2 t₂

-- Conversion of a list of key-value mappings to a tree.

open import Data.List.Base using (_∷_; [])

t₄ : StringsTree
t₄ = fromList ((2 , v₂) ∷ (1 , v₁) ∷ [])

------------------------------------------------------------------------
-- Queries

-- Let us formulate queries as unit tests.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Searching for a key.

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base as Maybe using (just; nothing)

q₀ : lookup t₂ 2 ≡ just v₂
q₀ = refl

-- Marshall's addition
q2val : Maybe.Maybe (Vec String 2)
q2val = lookup t₂ 2

q₁ : lookup t₃ 2 ≡ nothing
q₁ = refl

q₂ : (3 ∈? t₂) ≡ false
q₂ = refl

q₃ : (1 ∈? t₄) ≡ true
q₃ = refl

-- Turning a tree into a sorted list of key-value pairs.

q₄ : toList t₁ ≡ (2 , v₂) ∷ []
q₄ = refl

q₅ : toList t₂ ≡ (1 , v₁) ∷ (2 , v₂) ∷ []
q₅ = refl

q₅′ : toList t₂′ ≡ (1 , v₁′) ∷ (2 , v₂) ∷ []
q₅′ = refl

------------------------------------------------------------------------
-- Views

-- Partitioning a tree into the smallest element plus the rest, or the
-- largest element plus the rest.

open import Function.Base using (id)

v₆ : headTail t₀ ≡ nothing
v₆ = refl

v₇ : Maybe.map (Prod.map₂ toList) (headTail t₂) ≡
     just ((1 , v₁) , ((2 , v₂) ∷ []))
v₇ = refl

v₈ : initLast t₀ ≡ nothing
v₈ = refl

v₉ : Maybe.map (Prod.map₁ toList) (initLast t₄) ≡
     just (((1 , v₁) ∷ []) ,′ (2 , v₂))
v₉ = refl

------------------------------------------------------------------------
-- Marshall experiments

open import Data.Nat

StringTree = Tree (MkValue (Vec ℕ) (subst (Vec ℕ))) -- why Vec? Why same?

record Yo : Set where
  constructor MkYo
  field
    this : ℕ
    that : String

open Yo

yo1 = MkYo 5 "five"

import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder

empty-string-map : Map String
empty-string-map = Data.Tree.AVL.empty
-}
