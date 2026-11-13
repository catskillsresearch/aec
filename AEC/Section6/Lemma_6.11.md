# Lemma 6.11

Lemma 6.11 (An average criterion for descent). Let $A \to B$ have eligible sizes $\nu \le \mu$, and let $q = \mathrm{tp}(d/B)$ be actual, with $|d| = \sigma < \nu$. Choose $\chi \ge c(\sigma)$ below $\nu$. Suppose that a bounded sequence $I = (d_i : i < \kappa)$ in $A$, with $\chi + \aleph_0 < \kappa < \nu$, has majority value $q \upharpoonright Z$ on every query $Z \subseteq B$ of size at most $\chi$, with at most $|Z| + \aleph_0$ exceptions. Then $q$ is the free lift of its actual $\nu$-restriction to $A$.

**Same-level Lean form is done** for `SingleModelData` (`q.ν = μ`, recursion-closed tail). The proof is `infra_611_isFreeFrom` in [`AverageDescent.lean`](AverageDescent.lean): a fresh Lemma 6.9 code for `q.restrict`, the bridge `infra_611_bridge` (`infra_610_majority_eq_type` and `infra_610_majority_unique`), `infra_610_move_query` on parameter lists, and `infra_610_same_galois`. `IsFreeFrom` is the resulting `IsFreeLift`. Mixed levels $\nu < \mu$ are deferred.

**[Results.lean](Results.lean)**

@import "Results.lean"
