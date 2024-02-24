module DepNiche2predicate

import Data.Vect

data Niche : (idx : Nat) -> Type where
  MkNiche : (idx : Nat) -> Niche idx

-- Suggestion by kiana on Idris Discord about how to restrict incNiche to
-- Niches below.
-- https://discord.com/channels/827106007712661524/1210312619886645338/1210364657425186856

-- per kiana
data IsNiche : Type -> Type where
  ItIsNiche : IsNiche (Niche n)

{-
-- kiana's version:
incNiche : (a : Type) -> IsNiche a => Type
incNiche (Niche x) @{ItIsNiche} = Niche (S x)
-}

-- What's the deal with the at-sign and the =>  ?
-- dunham explained (Thomas Coding Cellist agreed) that 

{-
... @{ } is the version of { } that matches an auto implicit (or
possibly an implicit with no name, I've only seen it used with
autos).  and the => is sugar for {0 auto _ : ..} ->  so that's:

incNiche : (a : Type) -> {auto 0 _ : IsNiche a} -> Type
-}

{-
-- version using dunham info and following Brady's TDDI style
incNiche : (a : Type) -> {auto 0 prf : IsNiche a} -> Type
incNiche (Niche x) {prf} = Niche (S x)
incNiche notaniche {prf} = Void
-}

-- Hybrid version.  The @{} syntax is clearer than '{prf}'.
-- Note the auto arg goes after the initial niche arg since refs it
incNiche : (a : Type) -> {auto 0 prf : IsNiche a} -> Type
incNiche (Niche x) @{ItIsNiche} = Niche (S x)
incNiche _ = Void

creek = Niche 0
beaverpond = incNiche creek

oldniches : List Type
oldniches = [Niche 0, Niche 1]

newniches : List Type
newniches = [incNiche (Niche 0) @{ItIsNiche}, incNiche @{ItIsNiche} (Niche 1)] -- Note the proof argument can go in either order

newniches' : List Type
-- newniches' = map (incNiche @{ItIsNiche}) oldniches
-- newniches = map incNiche [Niche 0, Niche 1]
-- = [Niche 1, Niche 2] : List Type

{-
mymap : (f : Type -> {auto prf : IsNiche a} -> Type) -> List Type -> List Type
mymap f [] = []
mymap {prf} f (x :: xs) = ((\t => f t {prf}) x) :: mymap f xs
-}

-- mymap f [] = []
-- mymap f (x :: xs) = (f x) :: mymap f xs

-- newniches' : List Type
-- newniches' = mymap incNiche oldniches

oldvec : Vect 2 Type
oldvec = [Niche 0, Niche 1]

newvec : Vect 2 Type
-- newvec = map incNiche oldvec
