

  
----------------------------------------------
-- More basic experiment code

{-
-- Note I don't need a type sigs here:

str-envs = "pond" ∷ "forest" ∷ "field" ∷ []
str-dunlins = "Marie" ∷ "Ulrich" ∷ "Sonia" ∷ []

envs = Example.nest ∷ Example.no-nest ∷ []
dunlins = Example.grey ∷ Example.brown ∷ []

-- dummy version: returns the same envs every time
envs-at-t : (t : 𝕋) → List Example.E
envs-at-t t = envs

-- dummy version: returns the same dunlins every time
duns-at-t : (t : 𝕋) → List Example.D
duns-at-t t = dunlins


---? I got the following type signatur by initializing `hist`
--? and then running C-c C-d.  Why is D first, then E?
---? The def of History listed Env first.
---? Are the fields of a record listed alphabetically in a record's type?
---? For that matter, why are *those* the parameter types?  Why D and
---? not (List D) or (𝕋 → List D) ?
hist : System.History Example.D Example.E
hist = record { Env = envs-at-t; Dunlin = duns-at-t }

-}
