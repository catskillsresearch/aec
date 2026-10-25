# Order presentation

From [Theorem 2.6](Theorem_2.6.md).

Theorem 2.6 (Order presentation). Suppose $K$ has arbitrarily large models and $\mathrm{LS}(K) = \ell$. There are at most $\ell$ labels, each of positive finite arity, and a functor $E$ from nonempty linear orders and order embeddings to $K$ and strong maps, with the following properties.

1. Every element of $E(I)$ is a label evaluated on an increasing finite list from $I$. Equality and all structure relations and function values are determined by the labels and the order/equality pattern of the finitely many indices involved.

2. $E(I)$ contains distinct distinguished elements $(a_i)_{i \in I}$. An order embedding $f : I \to J$ sends $a_i$ to $a_{f(i)}$, and its action on any labeled element is position substitution.

3. For every finite nonempty $s \subseteq I$, the elements labeled on $s$ form a strong submodel $E_s(I)$ of cardinality at most $\ell$. For $s \subseteq t$ these submodels are strongly included, and $E(I) = \bigcup_s E_s(I)$.

4. $|I| \le \|E(I)\| \le |I| + \ell$. In particular, for every infinite $\kappa \ge \ell$, $K$ has a model of cardinality exactly $\kappa$.

Here a subpresentation is identified with its image under the canonical strong map when an inclusion of underlying universes is convenient.

**[OrderPresentation.lean](OrderPresentation.lean)**

@import "OrderPresentation.lean"
