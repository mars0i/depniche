-- Niche model based on Brady's hangman game in TDDI sect 9.2
module Hangman

import Data.Vect

-- Organism or pop has to guess the parameters that make up the niche.
data Niche : (guesses_remaining : Nat) -> (n_missing : Nat) -> Type where
  MkNiche : (params : Vect n Bool) -> (missing : Vect n_missing Bool) ->
          Niche guesses_remaining n_missing

-- If fails to find them all, fails to reproduce, or goes extinct.
data Finished : Type where
  Gone : (niche : Niche 0 (S n_missing)) -> Finished
  Persists : (niche : Niche (S guesses_remaining) 0) -> Finished


forage : Niche (S n_guesses) (S n_missing) -> IO Finished
forage st = ?forage_rhs

