# Orbit-record bound

From [Lemma 3.6](Lemma_3.6.md).

Lemma 3.6 (Uniform orbit bound). There is a fixed set $R_\theta$ of possible presentation records, depending only on $\ell$ and $\theta$, with

$$|R_\theta| \le B(\ell, \theta) := 2^{2^{\ell+\theta}}.$$

For every categoricity cardinal $\kappa \ge \max(\ell, \theta^+)$, the set of automorphism orbits of $\theta$-tuples in its model has cardinality at most $B(\ell, \theta)$. This applies also when $\kappa$ is singular. If $|\delta| = \kappa$ and $\mathrm{cf}(\delta) > \theta$, each realized record in $E(H(\delta))$ determines exactly one such model orbit.

**[OrbitRecordBound.lean](OrbitRecordBound.lean)**

@import "OrbitRecordBound.lean"
