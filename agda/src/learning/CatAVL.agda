-- Most of this is copied from
-- https://agda.github.io/agda-stdlib/v2.0/README.Data.Tree.AVL.html

{-# OPTIONS --cubical-compatible --safe #-}

module learning/CatAVL where

------------------------------------------------------------------------
-- Setup

-- AVL trees are defined in Data.Tree.AVL.

import Data.Tree.AVL

-- This module is parametrised by keys, which have to form a (strict)
-- total order, and values, which are indexed by keys. Let us use
-- natural numbers as keys and vectors of strings as values.

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Product.Base as Prod using (_,_; _,′_)
open import Data.String.Base using (String)
open import Data.Vec.Base using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality

open Data.Tree.AVL <-strictTotalOrder -- renaming (Tree to Tree′)
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

NatTree = Tree (MkValue (Vec ℕ) (subst (Vec ℕ)))

data Foo : ℕ → Set where
  foo : (n : ℕ) → Foo n

-- The first arg to MkValue is a function that returns a type.
-- See https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Beginner.20questions.20about.20Tree.2EAVL*/near/454365151

-- It can be an indexed data type, which in this context is a function:
FooTree = Tree (MkValue Foo (subst Foo))

substFoo = subst Foo

substFooProof = substFoo refl

-- Or it can b a normal function that returns a type, like this:
foobar : ℕ → Set
foobar n = Foo (suc n)

SucFooTree = Tree (MkValue foobar (subst foobar))

-- Or like this:
myvec : ℕ → Set
myvec n = Vec String n

MyVecTree = Tree (MkValue myvec (subst myvec))

substfoobar = subst foobar
-- moresubstfoobar = subst foobar (2 ≡ 2)

-- yow = substfoobar (2 ≡ (suc 1))

--------------------------------------


record Yo : Set where
  constructor MkYo
  field
    this : ℕ
    that : String

open Yo



------------------------------------------------------------------------
-- Further reading

-- Variations of the AVL tree module are available:

-- • Finite maps with indexed keys and values.

import Data.Tree.AVL.IndexedMap

-- • Finite sets.

import Data.Tree.AVL.Sets
