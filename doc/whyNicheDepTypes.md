whyNicheDepTypes.md
---
##### Thoughts about modeling niche construction using dependent types (or not).
This summarizes some current thinking, filtering and adding to earlier notes.

This is still just brainstorming.  If it stimulates work on something
interesting that is only indirectly related to what's below, that's
enough.

* I view modeling of an extremely complex system as in biology
  as involving idealization---sometimes very abstract ones---in
  order to approximate aspects of the system, and to understand
  some "dimensions" of its functioning.

* I don't think that the reality of niche construction in nature can
  be fully captured using dependent types in the simple way I had in
  mind.  But that's not the point.  The point is to use the model to
  approximate interesting patterns that might or that do exist in
  nature.

* Treating a niche as a type per se, yet that is modifiable by
  action by an organism, suggests a conceptualization that kind of fits
  with pre-niche-construction thinking about niches, but that
  allows niche construction.  This suggests another way of
  thinking about niche construction, rather than the kind of
  complex mess idea that Lewontin's view suggests (even though
  that might be the reality) and rather than just vagueness and
  case-by-case applications (which also might be more realistic).

* An organism is able to survive and maybe reproduce in
  environmental conditon (or niche) $1$, but might do so more
  successfully in a different one. In order for niche constructon
  to occur, the organism must be alive!  So if niches are types,
  an organism can have multiple types.  This isn't allowed in any
  simple way in a strictly typed language.  I thought about
  treating niches as typeclasses or interfaces, but it was
  complicated to think through, and it probably would cause
  problems because this kind of thing is not what these things
  are designed for.  So more recently I've been thinking about
  identifying an organism with abilities to use any member of a
  collection of niches.  In my very simple explorations of
  capabilities of dependently typed languages, started referring
  to the thing that the niche is a type of a "niche user" rather
  thabn an organism.  So then an organism is a collection of
  niche users.  (There's probably better terminology.)  (Here
  "organism" is intentionally ambiguous between a kind or set of
  organisms---maybe all members of a species---and an individual,
  token organism.)

* It's not necessary to use dependent types to do this kind of thing.
  You can do it in any language.  But the suggestive properties
  of dependent types is a plus.  It conveys an idea clearly.  (How
  valuable is that, though?  Choosing a language and a style of
  coding for that purpose?)

* We might want to implement an agent-based model and explore
  different configurations, look for interesting patterns, etc.
  (If so, there would be some benefit to using a language with an
  FFI that can easily interface to a nice ABM library.  The
  options are limited to popular languages such as Java, C++,
  Python.  There's one Javascript ABM library, but last I checked
  it wasn't very full-featured.  We can get a long way without
  an ABM library, but it's a nice thing.  There's a list of
  options here:
  https://en.wikipedia.org/wiki/Comparison_of_agent-based_modeling_software

* We might want to try to model a real system.  For that, though,
  it might be good to collaborate with people who have more
  knowledge of some systems than I do.  I think we could do it
  with just the two of us, but it requires more research.  I know
  some philosophers of biology who work on the border with
  biology, and who might be interested.  They might know
  biologists who'd want to get involved.  Or it might be possible
  to contact some biologists directly.  (I work on the border
  sometimes, but this is not the border I've been working at,
  lately.)

* If we have as part of an ideal result that scientists might use
  software that we develop (a long-shot), that might influence
  the choice of implementation language.

* Or we might just say that we know that people might prefer to
  write this kind of model in Python or something else, but it's easier
  to spell out the ideas clearly in (e.g.) Idris.

* Or if the models are promising, maybe it would be worth developing a
  tool that was easy to use.  This would be a way to sidestep
  resistance to using a dependently typed language, Haskell, etc.

* So suppose we build something that represents, in some abstract
  way, a biological process.  But programs are proofs, so we have
  "proven" something that is represented by the type system, and
  how it's applied in the functions representing biological
  relationships.  What is that?  What has been "proven"?  Maybe
  it won't be interesting to describe, but if it is, it might be worth
  writing about.  Maybe it will be no more interesting than
  a proof that there's a natural number, namely 42:

    ```haskell
    n : Nat
    n = 42
    ```
* *Very* unlikely, but: if it turned out that the patterns we're
  modeling had parallels in some pre-existing other domain, maybe
  something more central to the dependent types world--that would
  be cool.
