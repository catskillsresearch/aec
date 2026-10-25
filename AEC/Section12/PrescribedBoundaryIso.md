# Prescribed boundary isomorphism

From [Definition 12.1](Definition_12.1.md).

Definition 12.1 (A prescribed boundary isomorphism). Let $a$ be a finite ordered set of axes, and let $X^- = (X_s^- : s \subseteq a)$ and $X^+ = (X_s^+ : s \subseteq a)$ be systems of the same shape. A prescribed boundary isomorphism is a family

$$h_s : X_s^- \longrightarrow X_s^+ \quad (s \subsetneq a)$$

of pointed isomorphisms such that $h_t \restriction X_s^- = h_s$ whenever $s \subseteq t \subsetneq a$. This condition refers to the displayed inclusions. It does not add an assumption about intersections of two incomparable vertices inside the top.

**[PrescribedBoundaryIso.lean](PrescribedBoundaryIso.lean)**

@import "PrescribedBoundaryIso.lean"
