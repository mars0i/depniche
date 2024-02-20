brainstorm2.md
===

An organism's reproduction depends on the niche.

Organisms are able to change niches.  Or rather, create them.

You can do this imperatively, but there should be no reason you
can't do it functionally.

Well, on the other hand, if you want constructed niches to affect
organisms other than the constructing one, you have to do
something that's analogous to imperative.  Like e.g. you could
just update the whole world going from t1 to t2, and make it so
that other organisms are only allowed to interact with the the same
set of niches at t2.  That's functional, but it's like imperative in
that the world that is available to the organisms changes.

If it's spacial, this is basically an ABM.  Or if there are location
indexes at all, that's like an ABM.

So you could do it functionally, and if it's a functional language,
that will be the easiest thing--but there are complications with
running an ABM in a functional language.

(And you could do it imperatively if you're careful.  e.g. don't allow
race conditions; a niche modifier gets a lock on the niche, or
alternatively, two niche modifiers have cumulative effects.  (Maybe
that means neither has a useful niche.))


So e.g. using Idris or Haskell, you need a list or array or tree
or something of niches, which gets updated with new niches as
time goes on.
