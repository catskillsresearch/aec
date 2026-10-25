# Orbit name

From [§3.3 Bounded names for model orbits](3.3.md).

Choose a model $C_\kappa$ at each categoricity size needed in a given set-sized construction. On its $\theta$-tuple orbits put $p \to r$ when some strong self-map sends a representative of $p$ to a representative of $r$. This relation is reflexive and transitive: compose maps after using an automorphism to align the intermediate representatives. Choose an injection of the orbit set into the fixed cardinal $B = B(\ell, \theta)$, once for each $\kappa$. These are its orbit names. For any copy of $C_\kappa$, a tuple’s name is independent of the isomorphism used to $C_\kappa$, because two such isomorphisms differ by an automorphism.

For a suitable $\delta$ of size $\kappa$, let $F_{\kappa,\delta}$ be the partial function from $R_\theta$ to $B$ sending each realized record to its orbit name. The profile of this presentation consists of its named arrow relation and $F_{\kappa,\delta}$. The profiles belong to a fixed set of cardinality at most $2^B$; in particular this bound is independent of $\kappa$ and $\delta$.

**[OrbitName.lean](OrbitName.lean)**

@import "OrbitName.lean"
