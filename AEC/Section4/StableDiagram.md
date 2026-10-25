# Stable diagram

From [Proposition 4.2](Proposition_4.2.md).

Proposition 4.2 (Stable diagrams). There is a definable, nondecreasing cardinal function $t$, with $t(\sigma) > \ell + \sigma$ a categoricity cardinal for every infinite $\sigma$, having the following properties.

1. Tuples of length at most $\sigma$ in models of size at least $t(\sigma)$ have canonical diagrams. Equality of diagrams is preserved by every strong embedding between such models, and there are at most $B_\sigma$ diagrams at these lengths.

2. Diagrams include atomic diagrams, respect reindexing and restriction, and are compatible when the bound $\sigma$ is increased. We denote equality by $D(a; M) = D(b; N)$, suppressing the bound when it is understood.

3. If $\kappa \ge t(\sigma)$ is a categoricity cardinal, equality of diagrams between tuples in $\kappa$-models is implemented by a strong map between those models.

4. A possible diagram of a pair of tuples $(a, c)$, of total length at most $\sigma$, can be realized over any tuple with the diagram of $a$ in any categoricity model of size at least $t(\sigma)$. “Possible” means that the diagram occurs in a model in the domain of its definition.

**[StableDiagram.lean](StableDiagram.lean)**

@import "StableDiagram.lean"
