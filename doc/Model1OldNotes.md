

old notes:
for each env:
  * Reconstruct the dunlins in it (possible since at present dunlins don't
    have any data except the dunlin id and the env id, both of which are known
    to the env).  Later we'll need to be able to look up dunlins by id, or
    store the dunlins themselves in the env if there's a way to do that.
    CONSIDER STORING DUNLINS IN ENVS, BUT ONLY ENV IDS IN DUNLINS.
  * for each such dunlin:
      - use get-fitness to return the fitnesses for each
      - create fitness new dunlins of the same kind, and place them ... in some env,
        updating the env in the dunlin (and in the envs? then need a different type)
  * possibly kill some old dunlins
 


TODO:
The idea is to update the list of envs by replacing each env with one in
which dunlins are consed onto the env's list of dunlins.
TODO:
Should probably be replaced anyway with a using Maybe or a version
in which it's provable that the desired environment would be found.
add-generation : List Env → List Dun → Maybe (List Env)
add-generation envs [] = just envs
add-generation envs (dun ∷ duns) = {!!}



add-duns-to-envs envs (dun ∷ duns) = let maybe-env = lookup-env (dun-loc dun) envs
                                        in {!!} -- have to update the list of envs



old notes:
for each env:
  * Reconstruct the dunlins in it (possible since at present dunlins don't
    have any data except the dunlin id and the env id, both of which are known
    to the env).  Later we'll need to be able to look up dunlins by id, or
    store the dunlins themselves in the env if there's a way to do that.
    CONSIDER STORING DUNLINS IN ENVS, BUT ONLY ENV IDS IN DUNLINS.
  * for each such dunlin:
      - use get-fitness to return the fitnesses for each
      - create fitness new dunlins of the same kind, and place them ... in some env,
        updating the env in the dunlin (and in the envs? then need a different type)
  * possibly kill some old dunlins
 



Simple linear search to look up envs by env id, i.e. location.
Can be replaced -- with something more efficient if needed.
TODO?: Replace with version in which in which it's provable
that the desired environment would be found?
(Why not require that envs be listed in order, so we don't
need to examine their internal indexes?  To make it easier to
generalize to 2-D.)
add-duns : (parent : Dun) → (offspring : List Dun) → (envs : List Env) → Maybe (List Env)
add-duns _ _ [] = nothing  -- What happened to the envs?!?
add-duns _ [] envs = just envs  -- Parent failed to reproduce
add-duns parent offspring envs = just (add-duns-by-loc (dun-loc parent) offspring envs)
Not sure why Emacs is graying the previous two lhs's.  Seems like all cases are covered.



TODO:
The idea is to update the list of envs by replacing each env with one in
which dunlins are consed onto the env's list of dunlins.
TODO:
Should probably be replaced anyway with a using Maybe or a version
in which it's provable that the desired environment would be found.
add-generation : List Env → List Dun → Maybe (List Env)
add-generation envs [] = just envs
add-generation envs (dun ∷ duns) = {!!}



add-duns-to-envs envs (dun ∷ duns) = let maybe-env = lookup-env (dun-loc dun) envs
                                        in {!!} -- have to update the list of envs
