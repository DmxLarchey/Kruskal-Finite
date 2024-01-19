# The Kruskal-Finite library

This is a collection of tools based on the following notion of finiteness
- a type is finite if it is listable: there is a (computable) list collecting all its members
- a predicate is finite if its span is listable

There is a dependency with [`Kruskal-Trees`](https://github.com/DmxLarchey/Kruskal-Trees) because
in the [`finite.v`](theories/finite.v) file, we actually show that there are finitely many rose
trees (ie arbitrarily but finite branching trees) of a given (or bounded) number of nodes.
