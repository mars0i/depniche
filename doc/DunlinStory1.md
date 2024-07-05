DunlinStory1.md
---
Rationale for names, constructors, fields in some of the Agda files.

### Background

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

### Fake-dunlin story

#### Basic types

1. Depending on shape of beak, dunlins disturb mud more or less,
which affects growth of small organisms that dunlins feed on.

2. Dunlins only feed right along a line where the water is at the
right depth.  (In the real world this line changes as the tide
goes in and out.) Or perhaps in the ovreall environment we are
modeling, the tide pool is a narrow band.  Discrete locations are
labeled by non-negative integers.

3. Dunlins reproduce asexually. Or: we only modeling only
females, and assume that the genetic and ecological influences of
males remain near an average value, so that it can be ignored.

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

Dunlins also have id numbers to identify them over time.

One kind of dunlin depletes the food that it prefers, but
prepares the env for better feeding by the other kind of dunlin,
which then depletes the kind of food it prefers.  This happens
more, the more dunlins of a particular kind are in an
environment.  Growth of a food kind in an env tends to produce
similar conditions in adjacent environments.

#### Fitness and niche construction

Here's a sketch of a possible set of dunlin and environment transition
rules.

Note: I'm starting to wonder if the three environment types
should just be replaced with an index.  The same rules could be
implemented using `{0, 1, 2}`, but then they could easily
be extended.

##### Fitness

* `short-beak` dunlins have highest fitness in well-disturbed
environments, less or no fitness in `mildly-disturbed` environments,
and little or no fitness in `undisturbed` environments.

* `long-beak` dunlins have highest fitness in `undisturbed`
environments, less fitness in `mildly-disturbed` environments (because
their food is being depleted), and little or no fitness in
`well-disturbed` environments (because there is little food for them).

* TBD: How fitness works and what numerical values it has:

    * Is there a determinate number of offspring for each fitness
    value, or is it probabilistic?

    * Where do new dunlins appear? In the location of the parent? In a 
      neighboring environment?  Somewhere else (a nest area), after
      which they appear in a random location?

##### Niche construction and other environmental change

* `long-beak` dunlins turn `undisturbed` environments into
  `mildly-disturbed` environments, and turn `mildly-disturbed`
  environments into `well-disturbed .

* How quickly `long-beak` dunlins alter an environment could be a
  function of the number of dunlins in it. i.e. perhaps if there are
  two or more dunlins in an environment, then it can go directly from
  `undisturbed` to `well-disturbed` in one timestep.

* When there are no `long-beak` dunlins in a disturbed environment, it
  gradually reverts to less disturbed states.

* Alternatively, the rule could be that `short-beak` dunlins are what
  cause an environment more suitable for `long-beak` dunlins.

* *What happens if there are multiple dunlins in an env, and they are
  not of the same type?*

##### Movement ("niche choice")

* We could allow dunlins to "migrate" between environments.  What
  determines that?  Some possible rules:

    * Dunlins migrate randomly.

    * A dunlin that is not in its best environment, or that is in
      its worst environment, randomly chooses one of the two
      neighboring environments.

    * A dunlin that is not in its best environment, or that is in
      its worst environment, moves to a neighboring environment
      iff it that environment is better for that kind of dunlin,
      or iff it's two steps better (and randomly chooses a
      direction if both neighbors are equally good).

    * A simple rule would be that a dunlin that's in a zero-fitness
    environment moves to a random neighboring environment.

    * Or to the *best* neighboring environment, or random if they are
    equally good?  In that case, if the dunlin goes to an equally bad
    environment, does it remember not to go back to the one that was
    as bad on the previous timestep?  (Not in the simplest model, but
    this adding htis would make the model more realistic.)
	  
* Need to add death.  When does a dunlin die?  Do we store a
nutritional state counter? Or does it die the first time it gets
no food? Can it die of old age?

##### Proximity

* Maybe allow environments to influence their neighbors.  For
example, the rule could be that if $E_1$ is `well-disturbed` and
the neighboring environment $E_2$ is undisturbed, then in the
next timestep $E_2$ (and $E_1$?) will become `mildly-disturbed`. 
This is because the prey that is associated with the
`well-disturbed` state diffuse to neighboring environments.
Questions:

    * Does `mildly-disturbed` environment influence its neighbors?

    * Does the diffusion happen in the other direction? Does an
    `undisturbed` environment influence its neighbors?  This
    would be more complicated.)

    * With numeric indexes instead of constructor-based
    environment variants, averaging and more complicated formulas
    would be easy to implement.



#### Possible future enhancements

* Make fitness and inheritance more complex.

* A two-dimensional environment space.

* Indexed environment variants.

* More dimensions of environmental variation.

* Mutation: i.e. random changes from one dunlin variant to another.

* Indexed dunlin variants.

* Indexed dunlin variants with mutation. This could allow gradual evolution over time.

* Sexual reproduction.  But for that to be worthwhile, we might
want more complex "phenotypes".
