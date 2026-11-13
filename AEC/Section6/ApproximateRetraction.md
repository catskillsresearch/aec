# Approximate retraction

From [Corollary 6.16](Corollary_6.16.md).

Corollary 6.16 (Approximate retractions). For same-level $A \le B$ there are arrows $(r_i : B \to A : i < \mu)$ such that, for every $a \in A$,

$$\{i < \mu : r_i(a) \ne a\} < \aleph_0.$$

The maps are not asserted to fix all of $A$ at once.

**Done** for `SingleModelData` ([`ApproxRetractionProof.lean`](ApproxRetractionProof.lean)). Present `A` on `lvlOrder μ ×ₗ (ℕ ×ₗ lvlOrder μ)`. The index is the nonzero blocks, so it has cardinality `μ`, and block `0` only keeps both sides of every cut nonempty. On block `i`, Proposition 6.15's two-sided exhaustion (`infra_615_middle_exhaust`) embeds `B` over the complement; `E.map φᵢ` and the presentation equivalence return the arrow to `A`. Finite `termSupport` meets finitely many blocks, which is `almost_id`. Terminal-strip 6.15 is not the close.

**[ApproximateRetraction.lean](ApproximateRetraction.lean)**

@import "ApproximateRetraction.lean"
