# Proposition 9.1

Proposition 9.1 (Type correspondence under projection). Let $P : C \to D$ forget some components of systems. Suppose that both schemes satisfy the working package, that $P$ takes objects and arrows to objects and arrows, including mixed arrows, and that the following diagram comparison holds: for bounded tuples in the retained sorts, equality of their $C$-diagrams is equivalent to equality of their $D$-diagrams after projection. The comparisons are made at arities bounded at both levels when levels differ.

At sufficiently closed levels, restriction induces a bijection on types of bounded tuples in any fixed list of retained sorts, given by

$$
\mathrm{tp}_C(v/X) \mapsto \mathrm{tp}_D(v/PX).
$$

The parameters on the left are all of $X$, including its forgotten components. The bijection commutes with restriction and isomorphisms, and with free lifting along arrows, including mixed arrows when the tuple arities and the required testing bounds lie below the smaller level. It also takes witnessed free products to their projected witnessed free products.

**[Results.lean](Results.lean)**

@import "Results.lean"
