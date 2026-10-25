# Lemma 14.2

Lemma 14.2 (Choosing subcubes with prescribed supports). Suppose two systems $X^{-}$ and $X^{+}$ have the same cardinal assignment, and prescribed isomorphisms $h_t$ on their proper faces. Suppose their top is active and put

$$
\kappa = \max_{s \in L} \kappa_s, \qquad Q = \{s \in L : \kappa_s = \kappa\}.
$$

One can choose witnessing global basis partitions $(H^{-}_s)$ and $(H^{+}_s)$ such that

$$
h_s[H^{-}_s] = H^{+}_s \qquad (s \in L,\ s \subsetneq a).
$$

Fix such partitions. Let $\chi$ be a cardinal with $\gamma \le \chi < \kappa$ which bounds all $\kappa_s < \kappa$. Given at most $\chi$ requested elements in the finitely many vertices on both sides, there are subsystems $U^{\pm}$ inside $X^{\pm}$ with the following properties:

1. Each requested element belongs to its indicated vertex. Every vertex whose size is strictly below $\kappa$ is retained in full.

2. Their witnessing pieces are subsets $I^{\pm}_s \subseteq H^{\pm}_s$. They equal $H^\pm_s$ when $s \notin Q$, and have cardinality $\chi$ when $s \in Q$.

3. On every proper face, $h_t[U^{-}_t] = U^{+}_t$. If compatible subsystems have already been chosen whose witnessing pieces are subsets of these fixed partitions $(H^{\pm}_s)$, and whose total vertex sizes are at most $\chi$, their entire vertices can be included among the requests. Moreover, at every $s \in Q$ one can require exactly $\chi$ additional basis coordinates beyond those old selected pieces, on both sides. All resulting inclusions preserve the relative independence condition for system arrows.

**[Results.lean](Results.lean)**

@import "Results.lean"
