NicheNotes.md
----
Longer notes on current content of Niche.agda and possible future addtions.


---
#### Dec≡, is-in

The stdlib definition of `Dec` is somewhat difficult to
understand. PLFA gives this simpler one

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

Estep and Dstep both take both envs and dunlins as args, because
dunlins can modify (i.e. remove, create) the envs through niche
construction, and envs can modify the dunlins by (a) death, (b) birth,
and (c) modifying a dunlin's phenotype. 

Performing (c) in functional code is like a death and a birth,
except that there are properties specific to that dunlin that should
be carried over to the "new" bird

It will probably be useful for `Dstep`, at least, to give every dunlin
a unique identifier that can be transferred to its new instance.  That
facilitates transfer of properties, tracking history of a dunlin, and
dynamic visualization if that's desired.

---
#### Tracking relationships between environments and dunlins

We'll need to track relationships between dunlins and envs, and envs
and envs to keep track the following.

**What env is this dunlin in?**

(Maybe it would be useful at some point to represent a dunlin as in
multiple envs that capture different aspects of its location.  Not
sure)

**What dunlins are in this env?**

This matters because if one dunlin modifies the env its in, that can
affect the fitness of other dunlins in the same env.

1. We could maintain mutual pointers stored in envs and dunlins, with a
collection of pointers from an env to
dunlins, and a pointer from a dunlin to an env.  

2. Or we could add a third collection of structures to maintain the
relationships, relational-database-style.

I'm inclined toward the first option.  It means we have to define
special functions to update relationships, but it's one less data
structure, and querying a dunlin or environment for information about
the other will be easy.


---
#### Relationship between concurrent environments

Another issue: Are env 1 and env 2 next to each other?

Do we need a map of the 2-D or 3-D space? This might matter
because changes in an env can spread to adjacent envs.  

I don't think we should try to implement this initially.  Simpler to
ignore it. But maybe we should keep this in mind to avoid making it
difficult to implement later.




