module DepNiche1

import Data.Vect
import Data.List
import Decidable.Equality

interface HasNiche (nicheid : Nat) where
  noffspring : Nat -- simpler version: constant reproduction
  offspringdist : List Double -- probabilities, where number of offspring is index
  -- offspringdist : Vect n Double -- probabilities, where number of offspring is index

-- It would be nice to require that it be proven that the list of
-- probabilities sums to 1.


data Organism : (orgid : Nat) -> (niches : List (HasNiche nicheid)) -> Type where
  MkOrg : (orgid : Nat) -> (niches : List (HasNiche nicheid)) ->
          Organism orgid niches

-- not right
-- HasNiche Organism orgid niches where
--   noffspring ---
--   offspringdist ---


isProb : Foldable ps => (ps : List Double) -> Dec((sum ps) = 1)
isProb ps = ?aa

