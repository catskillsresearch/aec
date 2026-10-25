# Lemma 6.14

Lemma 6.14 (Closure of a bounded support set). Let $J \subseteq J^*$ be linear orders, let $V$ be a convex strip in $J^*$, and put $J_0 = J \setminus V$. Allow any fixed finite coloring of positions in $J_0$, including their side of $V$. Let $T^* \subseteq J^*$ and $S_0 \subseteq J_0$ be bounded sets. Given an infinite $\chi$, choose an infinite $\lambda$ with

$$
\lambda \ge \chi + |T^{*}| + |S_0|, \qquad \kappa = 2^{\lambda}.
$$

There is $S \subseteq J_0$, of size at most $\kappa$, containing $S_0 \cup (T^* \cap J_0)$, with this property: for every $R \subseteq S$ of size at most $\chi$ and every indexed tuple $Q$ of at most $\chi$ positions from $J_0$, there is an equally indexed tuple $Q'$ in $S$ having the same order, equality and color pattern over $R \cup T^*$. In particular all positions named by $R$ are fixed whenever they occur in $Q$. At a strong limit level with the displayed input bounded, $S$ is bounded. The assertion needs no well-order hypothesis on $J$.

**[Results.lean](Results.lean)**

@import "Results.lean"
