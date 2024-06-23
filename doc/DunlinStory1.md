DunlinStory1.md
---
Rationale for names, constructors, fields in some of the
Experiment?.agda files.

A speculative, made-up story based on a couple of articles about
dunlins or related birds: Depending on shape of beak, dunlins
disturb mud more or less, which affects growth of small organisms
that dunlins feed on or that become part of their gut microbiome.

Is the following compatible with the structure in Callan's code
in Niche.agda?  I think so.

Every dunlin has an environment, identified by an environment id
number.

Every environment contains zero or more dunlins.

Think of environment id numbers as simplified locations. At a
given location, only one environment type is possible.  However,
the type at that location can change.

By contrast, dunlins have id numbers because every organism is
unique.

(Another environment difference that could be included is
near-forest vs. far-from-forest.  Or maybe near-foliage, etc.  A
dunlin can "construct" such an environment by choosing to build
its nest there.  These differences can effect the probability of
predation and protection from wind.)

