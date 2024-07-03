DunlinStory1.md
---
Rationale for names, constructors, fields in some of the Agda files.

Dunlins are real shorebirds that sometimes feed on mudflats.
https://www.allaboutbirds.org/guide/Dunlin/
"They feed tend to feed on invertebrates just barely below the
surface" (of the mud under shallow water).  

"... most probe less than a quarter-inch deep.
 The prey they consume include earthworms, marine worms, midges,
 flies, craneflies, beetles, spiders, snails, blue mussels, small
 clams, and amphipods. Dunlin also eat small amounts of plant
 matter, mostly seeds. On rare occasions they eat tiny fish."
(from the life history page).

We are modeling fake shorebirds that we call "dunlins", though we
can take vague inspiration from scientific literature on real
dunlins.

Here's the fake-dunlin story: 

1. Dunlins eat either 

1. Depending on shape of beak, dunlins disturb mud more or less,
which affects growth of small organisms that dunlins feed on.

2. Dunlins only feed right along the a line where the water is at
the right depth. Discrete locations are labeled by non-negative
integers.

(Is the following compatible with the structure in Callan's code
in Niche.agda?  I think so.)

Every dunlin has an environment, identified by an environment id
number.

Think of environment id numbers as simplified locations. At a
given location, only one environment type is possible.  However,
the type at that location can change.

Every environment contains zero or more dunlins.  However, the
state of an environment can influence the state of the two
adjoining environments.

By contrast, dunlins need id numbers because every organism is
unique.

One kind of dunlin depletes the food that it prefers, but
prepares the env for better feeding by the other kind of dunlin,
which then depletes the kind of food it prefers.  This happens
more, the more dunlins of a particular kind are in an
environment.  Growth of a food kind in an env tends to produce
similar conditions in adjacent environments.

