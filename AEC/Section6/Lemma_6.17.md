# Lemma 6.17

Lemma 6.17 (Descent through approximate retractions). Let $A \le U$ be objects at an eligible level $\mu$, and let $A' \le U'$ be objects at an eligible level $\nu \le \mu$, with compatible arrows $A' \le A$ and $U' \le U$. Suppose there are arrows $(r_i : U \to A : i < \nu)$ such that every $a \in A$ is fixed for all but finitely many $i$, and $r_i [U' ] \subseteq A'$ for all $i < \nu$. Then for every tuple $d$ in $U'$ of length less than $\nu$, its actual type over $A$ is the free lift of $\mathrm{tp}(d/A'; U')$. All comparisons are comparisons of the working diagrams, including mixed-level diagrams at arities bounded at $\nu$.

**Done** for `SingleModelData` mixed `ν ≤ μ` ([`DescentRetraction.lean`](DescentRetraction.lean), thin wrap in [`Results.lean`](Results.lean)). Each `rᵢ` factors through `toA` by `factorEmbedding`. Same Galois type of the small and restricted large tuples is the commuting square (`toU` and `id`). A short subsequence of the restricted copies is an `ApproximationSequence` for `tp(d/A';U')`; majority on queries in `A` uses mixed saturation move-query plus almost-identity exceptions. Corollary 6.16 supplies families in applications but is not called in the proof. **Next tip:** Lemma 7.2.

**[Results.lean](Results.lean)**

@import "Results.lean"
