notesOnModel1.md
---
Notes #1 on a possible niche construction model


It's not enough to be able to read off Niche parameters from an
organism that will replace a Niche with a different Niche.  It should
be possible for an organism to modify a Niche that is not one of its
types.  Example:

A beaver affects the creek upstream and downstream from the dam
it makes.  So it modifies the enviromental conditions, niches, of
other organisms.  A beaver dam might (for all I know) have an
effect on something that is not part of its niche.  For example,
a beaver's range might not go very far below the dam, but water
flow might be affected far downstream.  (I haven't studied
this--seems plausible.)

That means a niche construction model has to allow modifications
to niches with parameters that are not associated with the
organism that's causing the change.  So it's necessary to be able
to read parameters from the collection of Niches---and you can't
do that without type-case---or get those parameters in some other
way.

One way is to store the parameters in a data element accessible
outside of the Niche type itself, but in a way that forces the type
and the externally accessible parameter to be the same, as in a
dependent pair or a datatype defined to be able to do what a dependent
pair does.

Another way is to use universe pattern codes that store the
parameters that are currently in the collection of niches.

When I asked about type-case in the Agda Zulip chat, Naïm
Camille Favier and Jacques Carette suggested something like the
universe pattern.  Naïm remarked that since Niche only had one
constructor, one might as well use the parameters (Nats, in my
example) as the codes representing Niches.  More generally, one could
use a product of numbers (or other things?) as universe codes, and
keep a collection of those that can be updated due to niche
construction by organisms.  One could still require that there only be
organisms that include instances of Niche types that are coded for by
elements in the collection of parameters.
