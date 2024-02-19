module DepNiche1

import Data.Vect
import Data.List

interface HasNiche (nicheid : Nat) where
  noffspring : Nat -- simpler version: constant reproduction
  offspringdist : List Double -- probabilities, where number of offspring is index
  -- offspringdist : Vect n Double -- probabilities, where number of offspring is index

-- It would be nice to require that it be proven that the list of
-- probabilities sums to 1.


data Organism : (orgid : Nat) -> (niches : List (HasNiche id)) -> Type where
  MkOrg : (orgid : Nat) -> (niches : List (HasNiche id)) ->
          Organism orgid niches

-- not right

HasNiche Organism where
  noffspring ---
  offspringdist ---
