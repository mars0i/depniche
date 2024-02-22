module DepNiche3

interface NicheUser (organism : Integer -> Type) where
  fitness : (nicheid : Integer) -> List Double

data Org : (orgid : Nat) -> (nicheid : Integer) -> Type where
  MkOrg : (orgid : Nat) -> (nicheid : Integer) -> Org orgid nicheid
