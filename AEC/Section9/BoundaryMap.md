# Boundary map

From [Definition 9.4](Definition_9.4.md).

Definition 9.4 (Boundary). For an $n$-axis object $J$, its boundary $\partial J$ consists of all the proper-axis projections $P_s J$, with their specified inclusions. For $n = 0$ the boundary is empty. A boundary map $h : \partial J \to \partial K$ is a compatible family of arrows $h_s : P_s J \to P_s K$ for proper $s$. A boundary isomorphism is such a family of isomorphisms.

Lists in a boundary are lists of occurrences in its vertex sorts. The diagram of a joint list records the specified inclusion maps and all resulting equalities. In particular, entries supplied from different faces can coincide in a containing vertex. Compatibility on the named subfaces alone is not asserted to settle these extra equalities; their preservation will be part of the next argument.

**[BoundaryMap.lean](BoundaryMap.lean)**

@import "BoundaryMap.lean"
