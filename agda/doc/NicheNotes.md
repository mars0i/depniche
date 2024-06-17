NicheNotes.md
----
Longer notes on current content of Niche.agda and possible future addtions.


---
#### Dec≡, is-in

The stdlib definition of `Dec` is somewhat difficult to
understand. PLFA gives this simpler one:

```agda
       data Dec (A : Set) : Set where
yes :   A → Dec A
no  : ¬ A → Dec A
```
Where ¬ is:
```
       ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
       ¬ P = P → ⊥
```

---
#### What do/should `Estep` and `Dstep` do?

Estep and Dstep both take both environments and dunlins as args, because
dunlins can modify (i.e. remove, create) the environments through niche
construction, and environments can modify the dunlins by (1) death, (2) birth,
and (3) modifying a dunlin's phenotype. 

Performing (3) in functional code is like a death and a birth,
except that there are properties specific to that dunlin that should
be carried over to the "new" dunlin.

It will probably be useful for `Dstep`, at least, to give every dunlin
a unique identifier that can be transferred to its new instance.  That
facilitates transfer of properties, tracking history of a dunlin, and
dynamic visualization if that's ever desired, especially if dunlins
move in space.

---
#### Tracking relationships between environments and dunlins

We'll need to track relationships between dunlins and
environments, and environments and environments to keep track the
following:

**What environment is this dunlin in?**

(Maybe it would be useful at some point to represent a dunlin as being in
multiple environments that capture different aspects of its location.  Not
sure)

**What dunlins are in this environment?**

This matters because if one dunlin modifies the environment it's
in, that can affect the fitness of other dunlins in the same
environment.  So we when one dunlin modifies an environment, we need
to find the other dunlins in that environment and update their
environments (which may change their fitnesses).

1. We could maintain mutual pointers stored in environments and
dunlins, with a collection of pointers from an environment to
dunlins, and a pointer from a dunlin to an environment.

2. Or we could add a third collection of structures to maintain
the relationships, relational-database-style.

I'm inclined toward the first option.  It means we have to define
special functions to update relationships, but it's one less data
structure, and querying a dunlin or environment for information
about the other will be easy.


---
#### Relationship between concurrent environments

Another issue: Are env 1 and env 2 next to each other?

Do we need a map of the 2-D or 3-D space? This might matter
because changes in an environment can spread to adjacent environments.  

I don't think we should try to implement this initially.  Simpler to
ignore it. But maybe we should keep this in mind to avoid making it
difficult to implement later.




