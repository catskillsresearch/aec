# Admissible family

From [Definition 11.1](Definition_11.1.md).

Definition 11.1 (Admissible shapes and geometric systems). Let $A$ be a finite linearly ordered set of axes. An admissible family $L \subseteq \mathcal{P}(A)$ of active labels is defined recursively. On no axes the family is $\{\emptyset\}$. If $k$ is a new last axis, choose an upward closed subset $Q$ of the previously constructed family $L$, and put

$$L' = L \cup \{s \cup \{k\} : s \in Q\}.$$

Here upward closed means that $s \in Q$, $s \subseteq t$, and $t \in L$ imply $t \in Q$.

**[AdmissibleFamily.lean](AdmissibleFamily.lean)**

@import "AdmissibleFamily.lean"
