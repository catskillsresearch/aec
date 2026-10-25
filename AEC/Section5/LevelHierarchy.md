# Level hierarchy

From [5.2 Refining the eligible levels](5.2.md).

Here is the hierarchy that will organize the two applications of Section 13. That section constructs one fixed bound majorant $\Phi$ for each application. Its initial class $G_0$ consists of the strong limit cardinals $\mu$ of countable cofinality with $\Phi(\alpha) < \mu$ for every ordinal $\alpha < \mu$; subsequent classes are

$$G_{j+1} = G_j \cap \mathrm{Lim}(G_j) \quad (j < \omega), \qquad G_\omega = \bigcap_{j < \omega} G_j.$$

This is advance notation: the definition of $\Phi$ and the proof that each $G_j$ is unbounded and closed under strictly increasing countable suprema are given in that section. A member of $G_{j+1}$ is thus both a member of $G_j$ and a limit of smaller members of $G_j$.

**[LevelHierarchy.lean](LevelHierarchy.lean)**

@import "LevelHierarchy.lean"
