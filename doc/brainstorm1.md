brainstorm1.md
===

#### Niches as organism types

A niche is a type, but it's indexed in one or more dimensions.
Indexes can be nats or fins.

> This requires programmer to specify in advance what range
of variation possible.  That differs from the natural world.

Here "organism" could mean an individual, or it could mean e.g. a
species or a variant within a species.

An organism type could be an indexed type to represent different
possible phenotypes of the same general kind of organism.

> Is this allowed by Haskell/Idris/Agda/Lean/etc?  Uh, need to have
> wrappers, I guess.  GADTs maybe.  Something like this? (Idrisey):
> ```haskell
> data Organism : (o : OrganismData) -> Organism
>   Niche0instance : (niche_index : Vect n Integer) -> Organism organism_data
>   Niche1instance : organism_data -> Organism organism_data
> ```

If there is no niche for an organism treated as a species or
variant, it goes extinct.

> So this means that whether a type exists can vary from run to run.
> Well that's OK if they are indexed types.

If there is no niche for an individual, it does not reproduce.

> OK, but this is weird.  If a niche is its type, how does it exist
> without a type?  I'm thinking this is more complicated to do with
> static types than I thought.  Maybe not worth the trouble. (?)
> Maybe the idea of representing niches by types per se---i.e. types
> at the language level---is a bad idea.

There may be one niche, or a list of niches, or spatially indexed
niches--i.e. we can have a 1-D, 2-D, or 3-D structure with
locations in which one or more niches can be located.  

Since types as such can't be duplicated, the way to do this is to
use locations as arbitrary type indexes.  Then a niche is any type s.t. the
non-location characteristics are correct for an organism.

> This doesn't seem to solve the problem with the dependent-types
  representation of niches, that an organism can fill different
  niches.  Because if an organism has type `Niche nicheindex
  nichelocation`, it doesn't have type `Niche nicheindex'
  nichelocation'`.  Right?

> OK, but this is what Haskell typeclasses or Idris interfaces are
> for.  They let multiple types be subtypes.  So if you say that an
> organism has to satisfy an interface, it can do that using different
> types.  Q: Are interfaces dependent types?  Can they be indexed?
> (And if not, maybe Haskell is just as good as Idris.)
> Also note that on a podcast---maybe where Aaron Stump was a
> guest?---there was talk of a language in which something could be an
> instance of multiple types.  There was a name for that.

> Here's an answer from TDDI p. 183:


>> If you know Haskell, you’ll be familiar with Haskell’s
concept of type classes. Interfaces in Idris are similar to type
classes in Haskell and are often used in the same way, though
there are some differ- ences. The most important are, first, that
interfaces in Idris *can be parameterized by values of any type,
and are not limited to types or type constructors*, and, second,
interfaces in Idris can have multiple implementations, though we
won’t go into the details in this chapter. [emphasis added]

So maybe treat an organism type as an Idris interface, and then
it can be an instance of any niche type that satisfies that
interface.  (Sounds slightly backwards, but kinda makes sense.)



If an organism can satisfy multiple niches, then some niches may
be more salutary than others for a given organism.

If an organism can satisfy multiple niche, one of the following
holds, in increasing complexity of models:

* The organism reproduces or not iff it has a niche. i.e. reproduction
  is Boolean.
* The organism reproduces with quantity n as a function of which niche
  it is able to fill.
* The organism-niche match generates a vector p representing a
  probability distribution over offspring counts, and the organism
  produces n offspring with probability p[n].

Note that if more than one kind of organism can fill a given
niche, the reproductive result might be a function both of the niche
and of the organism's type.

---

The following uses Kaiser and Trappes' NC$^3$ vocabulary.

#### Niche construction

An organism can "modify" a niche--i.e. generate a new niche
object with different indices.  This may replace the old niche or
be added to ther collection of niches, or to a collection at a
different location.

#### Niche choice

An organism can select a better (or worse) niche, perhaps by selecting a
location.  (There might be selection on such choices.)

#### Niche conformance

An organism can modify its phenotype so that it then satisfies a
different niche, if it has an indexed type.

---

#### The hangman model

Brady's chapter 9 hangman game could be a starting point for niches in
which the organism must search for niche parameters that will make it
successful.  The number of guesses is the time until failure.  (If you
want, you could add guesses for e.g. finding food.)

#### Beyond niches

Niche choice could involve foraging.  In fact, you can think of food or a
mate as an "individual niche".

#### Why this matters

Maybe it doesn't, but ...

##### Conceptual order from chaos

Thinking Lewontin-style and FLOS-style makes organism-environment
interactions into a complex system---and it's complex to think about.
That's the reality, but:

This kind of model allows the flexibility to model a lot of the
interactions in the real world, while imposing a clear
distinction between salutary environmental conditions and
organism.

In that sense it can simplify thinking.  

Moreover, it can cover lots of different situations.

Although it could also distort thinking---by forcing thinking into
a niche vs organism conceptualization.

##### Computer model correctness

Bugs are bad for scientific conclusions.

I think dependent types are too much work in general for
scientific modeling, in this case there other payoffs--see #1.
