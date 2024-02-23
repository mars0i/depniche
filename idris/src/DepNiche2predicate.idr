module DepNiche2predicate

-- Suggestion by kiana on Idris Discord about how to restrict incNiche to
-- Niches.
-- https://discord.com/channels/827106007712661524/1210312619886645338/1210364657425186856

data Niche : (idx : Nat) -> Type where
  MkNiche : (idx : Nat) -> Niche idx

data IsNiche : Type -> Type where
  ItIsNiche : IsNiche (Niche n)

incNiche : (a : Type) -> IsNiche a => Type
incNiche (Niche x) @{ItIsNiche} = Niche (S x)

newniches : List Type
newniches = map incNiche [Niche 0, Niche 1]
-- = [Niche 1, Niche 2] : List Type

-- What's the deal with the at-sign and the =>  ?
