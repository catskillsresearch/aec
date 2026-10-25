# Piece rank

From [Definition 14.1](Definition_14.1.md).

For $t \subseteq a$ let $a_L(t)$ be its largest active subset. The span identities and monotonicity imply

$$\mathrm{rk}\, P(X_t) = \max\{\kappa_s : s \in L,\, s \subseteq t\} = \kappa_{a_L(t)}.$$

All these ranks are at least $\gamma$, so Corollary 10.10 shows that the same formula gives $\|X_t\|$.

**[CardinalAssignment.lean](CardinalAssignment.lean)**

@import "CardinalAssignment.lean"
