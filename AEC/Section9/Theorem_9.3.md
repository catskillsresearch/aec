# Theorem 9.3

Theorem 9.3 (Finite marked systems). Start with the single-model scheme, allowing fixed bounded named data of a fixed diagram. Let $r$ be a prescribed, definable, isomorphism-invariant stationary type of a finite tuple in its root sort. Stationarity here includes free lifting under mixed arrows at eligible levels. For each finite $n$, the $n$-fold marked increment construction gives a working scheme $C_n$ at sufficiently closed levels. Its objects are systems indexed by the subsets of ${1, \ldots, n}$, with the prescribed marks and componentwise strong arrows.

For $s \subseteq \{1, \ldots, n\}$, retaining the axes in $s$ in their induced order gives a projection

$$
P_s : C_n \to C_{|s|}.
$$

Every such projection takes objects and arrows to objects and arrows, including mixed arrows, and preserves and reflects diagram equality on bounded tuples in its retained sorts. It consequently has the exact type correspondence of Proposition 9.1. The type in the root sort lying over $r$ exists uniquely over every whole system and lifts freely. These conclusions include the projection to the base root and each single-axis projection. In a single-axis projection the upper object is all-dominated over its lower object together with the prescribed mark; forgetting other axes does not remove that assertion.

**[Results.lean](Results.lean)**

@import "Results.lean"
