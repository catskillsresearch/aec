# Approximation sequence

From [Definition 6.8](Definition_6.8.md).

Definition 6.8 (Approximation sequence). An approximation sequence for $p = \mathrm{tp}(v/A)$ at query size $\tau$ is an indexed family $I = (v_i : i < \kappa)$ in $A$, each $v_i$ having the same index set as $v$, such that the concatenation of the family is bounded and, for every $Z \subseteq A$ of size at most $\tau$,

$$\{i < \kappa : D(v_i, Z) \ne p \restriction Z\} \le |Z| + \aleph_0.$$

Here $p \restriction Z$ denotes its joint diagram, and a sequence is always indexed: different indices may carry the same tuple. We use the same terminology for all projections of the displayed tuple.

**[ApproximationSequence.lean](ApproximationSequence.lean)**

@import "ApproximationSequence.lean"
