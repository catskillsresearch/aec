# Continuity condition

From [Definition 7.7](Definition_7.7.md).

Definition 7.7. A bounded marginal type $p$ satisfies the continuity condition used here if the following holds at every sufficiently closed eligible level to which $p$ is freely lifted. Suppose

$$X_0 \le X_1 \le \cdots \le X_i \le \cdots \quad (i < \delta)$$

is a continuous chain at that level, its union is an object at that level, and a fixed realization $b$ in a coupled extension satisfies

$$\mathrm{tp}(b/X_i) = \mathrm{tp}(b/X_0)^{\mathrm{fr}}_{X_i} \quad (i < \delta).$$

Then the same equality holds over $\bigcup_{i < \delta} X_i$. The type at $X_0$ is required to be the appropriate free lift of $p$.

**[ContinuityCondition.lean](ContinuityCondition.lean)**

@import "ContinuityCondition.lean"
