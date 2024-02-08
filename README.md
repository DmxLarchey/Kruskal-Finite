```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)
```
[comment]: # ( ∀ → ∃ ⋀ ⋁ ⇒ )

# What is this library?

This is a collection of tools based on the following notion of finiteness
- a type is finite if it is listable: there is a (computable) list collecting all its members
- a predicate is finite if its span is listable

# Dependencies

There is a dependency with [`Kruskal-Trees`](https://github.com/DmxLarchey/Kruskal-Trees) because:
- in the [`finite.v`](theories/finite.v) file, we prove finiteness results about the types `idx n` and `vec X n` which are actually defined in `Kruskal-Trees`;
- in the [`examples/trees.v`](theories/examples/trees.v), we moreover show that there are finitely many rose trees (ie arbitrarily but finite branching trees) of a given (or bounded) number of nodes, and we need `rtree X` and `ltree X` (and also `list_sum`).

# How to install

This library is CI tested with Coq `8.14`-`8.18` and should install smoothly with `opam install coq-kruskal-finite`.
