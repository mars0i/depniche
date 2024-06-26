DunlinStory1.md
---
Rationale for names, constructors, fields in some of the
Experiment?.agda files.

Dunlins are real shorebirds.  We are modeling fake shorebirds that
we call "dunlins".  But there is some vague inspiration from scientific
literature on real dunlins.

Here's the fake story: 

1. Depending on shape of beak, dunlins disturb mud more or less,
which affects growth of small organisms that dunlins feed on or
that become part of their gut microbiome.

2. Dunlins only feed right along the high tide line.  Discrete
locations are labeled by non-negative integers.

Is the following compatible with the structure in Callan's code
in Niche.agda?  I think so.

Every dunlin has an environment, identified by an environment id
number.

Think of environment id numbers as simplified locations. At a
given location, only one environment type is possible.  However,
the type at that location can change.

Every environment contains zero dunlins or one dunlin.  However,
the state of an environment can influence the state of the two
adjoining environments.

By contrast, dunlins need id numbers because every organism is
unique.

