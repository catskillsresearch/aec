# Joint freshness

From [Definition 11.8](Definition_11.8.md).

Fix pieces $(H_s^X : s \in L)$ in a system $X$. For an arrow $X \to Y$, extend them to pieces

$$H_s^Y = H_s^X \cup\!\!\cdot\, C_s^Y.$$

The sets $C_s^Y$ are its complementary pieces. Their sizes may be any cardinals at most $\mu$, including zero, even though all the total pieces have size $\mu$.

Definition 11.8 (Joint freshness). A list of coordinates in an extension $Y$ of $X$, with individual active labels, is jointly fresh over $X$ if it is a sublist of the complementary pieces for some such extension of the pieces of $X$. At a single label $s$, the corresponding condition is independence over

$$\mathrm{cl}\big(P(X_s) \cup D_s(Y)\big).$$

For several labels these relative conditions assemble into joint freshness by Lemma 11.4. Coordinates are regarded as occurrences in their designated vertex sorts.

**[JointFreshness.lean](JointFreshness.lean)**

@import "JointFreshness.lean"
