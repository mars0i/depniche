module DepNiche

test : String
test = "Hello from Idris2!"

data Reproducer : Type where
  Reprod : Reproducer

data Niche : String -> Type where
  MkNiche : (name : String) -> Niche name
