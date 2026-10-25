# 11 Geometric systems and classification by bases


Throughout this section the distinguished model$M_{0},$its fixed pointed pattern, and the pregeometry P are those of Proposition 10.6 and Theorem 10.5. All model sizes exceed the threshold of Corollary 10.10. Thus a strong inclusion of pointed models with equal P-sets is equality. At an eligible uniform level µ, all vertices have size µ. A statement about unions of objects at that level concerns chains whose total size is µ, as in the working conditions of Definition 5.2.

We first prove structural and presentation assertions without assuming categoricity of systems. The classification argument then proceeds by the number of axes. Its first assertion extends a root isomorphism and prescribed bijections of the other basis pieces; this gives categoricity for the current shape. That categoricity supplies the working package used to prove the second assertion: prescribed bijections of the basis pieces added to a fixed system extend to an isomorphism over that system. By splitting off the last axis, the second assertion gives the first at the next dimension. We establish the conditional package before carrying out this paired induction.

## 11.1 Shapes, relative bases, and arrows

Definition 11.1 (Admissible shapes and geometric systems). Let A be a finite linearly ordered set of axes. An admissible family L ⊆ P(A) of active labels is defined recursively. On no axes the family is {∅}. If k is a new last axis, choose an upward closed subset Q of the previously constructed family L, and put L' = L ∪ {s ∪ {k}: s ∈ Q}.

Here upward closed means that s ∈ Q, s ⊆ t, and t ∈ L imply t ∈ Q.

A geometric system of shape L is a family$(X_{t}: t ⊆$A) of pointed models in a common top model, with$X_{t} ≤_{K} X_{u}$when t ⊆ u, satisfying the following condition. There is a partition$(H_{s}: s ∈$L) of a basis of$P (X_{A})$such that$H_{s} ⊆ P (X_{s})$and

()

$P (X_{t}) = cl_{P(X_{A}})$(s∈L,⋃s⊆t$H_{s})$(t ⊆ A). (12)

At uniform level µ we require$|H_{s} | =$µ for every s ∈ L. The resulting scheme is denoted$G_{L}.$The basis partition witnesses the definition; it is not named in the system structure.

For a vertex t, write

$D_{t}$(X)$= cl_{P(X_{A}}) ($(r⊊t⋃$P (X_{r}))).$

For t = ∅ this is the closure of the empty set in the pregeometry. An arrow X → Y is a commuting family of pointed strong embeddings for which a witnessing partition for X extends to a witnessing partition for Y. Equivalently, after identifying X with its image, each finite tuple from$P (X_{t})$independent over$D_{t}$(X) remains independent over$D_{t}$(Y).

The equivalence in the last sentence, including its independence from the initially chosen partition, will be proved below. All closures and independence assertions are computed in a common containing pointed model. Theorem 10.5 makes this convention independent of the chosen common strong extension. The notation$cl_{P(X_{A}})$means the closure$cl_{X_{A}}$defined there; its subscript emphasizes the pregeometry in which it is computed. We omit that subscript when the ambient model is clear.

Lemma 11.2 (Combinatorics of shapes). An admissible family contains ∅ and is closed under unions. Its restriction to any subset of the axes is admissible, with the inherited order. Consequently every t ⊆ A has a largest active subset

⋃

$a_{L}$(t) = {s ∈ L: s ⊆ t}.

In a geometric system,$X_{t} = X_{a_{L}}$(t) whenever t is inactive.

Proof. The union assertion follows by induction on the axes. Unions of old labels are old. If a union involves s ∪ {k} with s ∈ Q, its old part is an active label containing s, and therefore belongs to Q. This also handles the union of two labels containing k. Restriction to a set of axes replaces L and Q, at every retained step, by their restrictions. The restricted Q is upward closed in the restricted L. Steps on discarded axes make no contribution. This proves the restriction assertion.

The displayed union is an active label, since the family is finite and contains ∅. The collections of active labels below t and below$a_{L}$(t) agree. Equation (12) therefore gives equality of their P-sets. The inclusion$X_{a_{L}}$(t)$≤_{K} X_{t}$and Corollary 10.10 give equality of the models.

Remark 11.3. Union closure alone would not imply the recursive last-axis description. For example, {∅, {1, 2}} is union closed, but its two layers on splitting off axis 2 have different active families. We use the recursive definition, including the upward closed set Q, when identifying a system with an arrow between systems on fewer axes.

Lemma 11.4 (Replacement and extension of relative bases). Suppose X is a geometric system. For each active s, choose any basis$B_{s}$of$P (X_{s})$over$D_{s}$(X). Then the$B_{s}$form a witnessing partition for X.

A componentwise strong system embedding is an arrow precisely when it preserves the relative independence in Definition 11.1. For an arrow, every witnessing partition of its domain extends to one of its codomain.

Proof. Fix a witnessing partition$(H_{s}: s ∈$L), and enumerate L in an order extending inclusion. For active s,

$D_{s}$(X) = cl ( (u∈L,⋃u⊊s$H_{u})).$

When the piece at s is replaced, previously processed labels not below s are independent, together with the original piece at s, over this lower span: they are parts of a single independent set. Replacing$H_{s}$by any basis of the same flat over its lower span preserves both independence and the span of the union. Explicitly, let C be the current pieces below s. Then cl(C$∪ B_{s}) =$cl(C$∪ H_{s}) = P (X_{s}),$and$C ∪ B_{s}$is independent. The remaining current pieces were independent over cl(C$∪ H_{s}),$since the full current partition was independent. They remain independent over the equal flat cl(C$∪ B_{s}).$Thus the new full partition is independent and has the same span. Applying this replacement at the finitely many active labels gives the first assertion and Equation (12) for the new partition.

If pieces extend along an embedding, any finite independence calculation in a vertex over its lower span is the same calculation using the corresponding pieces in the larger independent set. Relative independence is therefore preserved.

Conversely, let$(B_{s})$be an arbitrary witnessing partition of the domain, viewed as a subsystem of Y. Preservation implies that$B_{s}$is independent over$D_{s}$(Y). Extend it to a relative basis$B_{s} ∪ C_{s}$of$P (Y_{s})$over$D_{s}$(Y). The first assertion, applied to Y, says that these choices assemble into a witnessing partition of Y. This proves both the equivalence and the final assertion.

Lemma 11.5 (Structural properties and the last-axis description). Arrows compose and satisfy coherence. Same-level chains of total size the level have unions in$G_{L},$with the common-upperbound clause also for arrows into a larger eligible level.

Restriction to any subset of axes preserves systems and arrows. If L' = L ∪ {s ∪ {k}: s ∈ Q}, splitting off the last axis identifies a system of shape L' with an arrow X → Y in$G_{L}$such that the complementary piece at s has size µ for s ∈ Q and is empty for s ∈/ Q.

Proof. Composition follows from the relative independence criterion. For coherence, suppose X ⊆ Y, and both embed by arrows in Z. Independence over$D_{t}$(X) implies independence over$D_{t}$(Z), and hence over its subset$D_{t}$(Y). Componentwise coherence is the AEC coherence axiom.

For a continuous chain, extend witnessing pieces successively using Lemma 11.4, and take their unions at limit stages. Every finite independent sublist and every finite dependence witness occurs at a stage. The resulting union pieces are independent and span every vertex of the componentwise union. Each contains µ elements from the first stage and has size at most µ, so all pieces still have size µ. For a chain which is not initially continuous, insert its earlier unions: the preceding construction applies recursively, and the common-upper-bound argument in the next paragraph supplies its connecting arrows.

If each stage maps by an arrow into Z, a finite tuple independent over the lower span of the union is independent over the lower span at any stage containing it. Its image is independent over$D_{t}$(Z). The componentwise AEC common-upper-bound axiom supplies the strong maps, so the union map is an arrow. This argument also permits a larger level for Z.

On restricting to axes B ⊆ A, retain the pieces whose labels are contained in B. They are a basis of$P (X_{B})$and satisfy the required span identities. For a retained vertex all its proper subsets are still retained; its relative independence test is therefore exactly the old test.

Finally let Z have shape L', and put$X_{s} = Z_{s}$and$Y_{s} = Z_{s∪{k}}. A$partition for Y is obtained by combining$H_{s}$with$H_{s∪{k}}$when s ∈ Q, and using$H_{s}$alone otherwise. These choices extend the pieces of X, and their complements have the asserted sizes. Conversely, extend pieces of X to pieces of Y along such an arrow, give the old pieces labels s and their complements labels s ∪ {k}, and use X and Y as the two layers. The span identities give a system of shape L'. Inactive vertices cause no exception, by Lemma 11.2.

For later use, preservation of relative independence also preserves finite rank calculations modulo the lower span. For finite tuples a, c in a vertex, the condition that a be independent over$D_{t}$(X) ∪ c is determined by the ranks, modulo$D_{t}$(X), of sublists of a, c. These ranks are determined by which sublists are independent. Thus arrows preserve this condition as well.

## 11.2 Order presentations and their rank

Proposition 11.6 (Tiled presentations). Let L be admissible and let µ be sufficiently large for the pointed pregeometry and the no-proper-pair conclusion. The order template E gives a presentation in$G_{L}$as follows. Choose a fixed initial order carrying the whole enumeration of$M_{0}.$For each active label t, choose a tile$T_{t},$preceded by a buffer$B_{t},$and concatenate these finitely many pairs after the initial order, in any fixed order. Every tile and buffer is a dense linear order without endpoints of size µ. In vertex s retain the initial order, all buffers, and just the tiles with labels t ⊆ s.

These presentations have the following properties.

1. Each active relative piece has rank µ.

2. Order embeddings of the corresponding tiles and buffers, fixing the initial pointed data, induce arrows, including between different eligible levels.

3. A presentation has an extension by an arrow gaining µ independent complementary coordinates at every active label simultaneously.

4. Tiles may be chosen with µ pairwise disjoint convex substrips, each of size µ. Further insertions of such substrips preserve the preceding assertions and the naturalness of the underlying K-diagrams.

No categoricity assumption about$G_{L}$is used here.

Proof. Let$I_{s}$be the indicated suborder and set$X_{s} = E(I_{s}),$using the literal embeddings supplied by Theorem 2.6. All$I_{s}$have size µ, since they contain all buffers. The models have size µ and are strongly included according to their labels. The initial order was chosen to contain the supports of the fixed enumeration of$M_{0}.$Its unchanged term pattern carries the same pointed model in every vertex, and coherence gives the required strong inclusion of$M_{0}.$

Choose a relative basis$H_{s}$of$P (X_{s})$over the union of its proper lower P-sets for every active s. We first prove that the indexed family of these choices is independent; this also proves that the pieces are disjoint. Suppose there is a finite circuit of labeled entries, allowing a two-entry equality dependence when two differently labeled entries coincide. Choose a maximal label s represented among its entries. Retain the finite term supports of all entries with label s, and indeed retain every support position in a tile available at s. In each unavailable tile replace all support positions by distinct positions in its preceding buffer, beyond all the finitely many retained positions in that buffer. Such positions exist because the buffer has no greatest point and is dense. No retained position lies in that unavailable tile. Consequently this replacement preserves the order and equality pattern of all circuit supports and fixes the whole initial pointed order.

The labels and this order pattern preserve the pointed finite geometry comparisons. One can formulate this either using the natural K-diagrams or by taking the term model on the fixed initial order and the finite supports and applying its two pointed strong embeddings into the original presentation. In the latter formulation Theorem 10.5 preserves and reflects the independence relation.

An entry with label t ̸= s in the circuit has no label properly containing s, by maximality. Thus s ⊈ t. After the replacement its term uses only common buffers, initial data, and tiles with labels contained in s ∩ t. Its image belongs to$P (X_{s∩t}) ⊆ D_{s}$(X). The entries with label s have not moved. The preserved circuit makes a sublist of$H_{s}$dependent over$D_{s}$(X), a contradiction. The union is therefore independent. It spans every vertex by induction on the labels: its relative basis spans that vertex over lower vertices, which have already been spanned. If a vertex is inactive, the order retained there is exactly the order retained at its largest active subset. This proves the decomposition without first assuming the system axioms.

We give the fresh-skeleton observation needed for the rank assertion. If J ⊆ I and i ∈ I \ J, the skeleton entry at i does not belong to E(J). Otherwise it equals a labeled term on a finite tuple of positions from J. Enlarge the order by a second position i' having the same order pattern as i relative to that finite tuple. Literal pattern preservation would make both distinguished skeleton entries equal to that term. This contradicts their required distinctness. The enlargement need only duplicate the cut relative to the finite tuple, not the cut relative to all of J.

For an active t, omit$T_{t}$from$I_{t}.$The resulting order still has size µ, contains the pointed data and all proper lower vertices, and presents a strong submodel. Enumerate µ points of$T_{t}$and adjoin them one at a time. The fresh-skeleton observation makes each successor inclusion proper. All these models have size µ, because the buffers were retained. By Corollary 10.10, each successor adds a point of P. Choose one such point at each successor. Relative closedness of P in strong submodels makes these choices independent over the initial omitted-tile model. There are µ choices, so the rank over the proper lower vertices is at least µ. It is at most µ by the size of$X_{t}.$This proves the first assertion, including the root case t = ∅.

Next consider componentwise order embeddings into enlarged tiles and buffers, identifying the source with its image. Suppose a finite tuple a in$P (X_{s}),$independent over$D_{s}$(X), becomes dependent over$D_{s}$(Y). Dependence has a finite witness consisting of points from proper lower vertices of Y. Fix the finitely many old positions supporting a. Move every other position needed for the witness into its corresponding old tile or buffer, preserving its order relative to the fixed positions. Density and absence of endpoints of the old order suffice for each finite pattern; it is not necessary that the old order be dense in the enlarged order. The initial pointed order remains fixed. Each witness remains in its designated proper lower vertex, now in X, and its finite dependence diagram is preserved. This contradicts independence of a over$D_{s}$(X). Lemma 11.4 therefore gives an arrow. The proof did not require equal source and target sizes.

To obtain simultaneous gains, enlarge all tiles with µ fresh points and, if desired, enlarge the buffers. For a particular active t, begin the strict-growth argument over the order containing the old t-tile, all enlarged proper-lower tiles, all enlarged buffers, and the initial data. This base contains$X_{t}$and all proper lower vertices of Y. Adjoining the fresh points of the t-tile yields µ independent points over that larger base. Hence the complementary rank at t is µ. The preceding arrow assertion allows any old pieces to extend, and Lemma 11.4 combines the relative choices into one partition. This proves the simultaneous assertion.

Finally a lexicographic sum, indexed by a linear order of size µ, of dense endpoint-free orders of size µ is still dense and endpoint-free and has size µ. Its summands are the desired convex substrips. In particular, for a presentation indexed by a well-order H, one can use H × Q and reserve intervals of H of order type and cardinality µ. Taking H of order type µ · µ supplies µ disjoint such intervals. Additional summands or strips do not change any of the preceding arguments. Underlying K-diagrams remain natural because the entire system was obtained by designated term subcollections of the single template E.

## 11.3 Obtaining the working package from categoricity

Proposition 11.7 (Conditional working package). Fix an admissible shape L. Suppose that$G_{L}$is categorical at every level in an unbounded class of eligible levels closed sufficiently for the preceding constructions. Assume also the eligible-subclass hypothesis of Convention 5.3. On an unbounded further class of sufficiently closed levels, it satisfies the full working package of Definition 5.2, with its actual system isomorphisms and its arrows from Definition 11.1. The resulting diagrams, saturation, and calculus include mixed arrows between eligible levels, and the output class retains the eligible-subclass hypothesis.

The closure requirements are uniform in the finite shape and the fixed pointed template. They use only the smaller and larger input levels specified by the general working-package construction.

Proof. The structural conditions are Lemma 11.5. Proposition 11.6 supplies term presentations and mixed presentation arrows before categoricity. By the assumed categoricity, every object at an input level is isomorphic to its presentation.

We check the extra relative-basis condition throughout the reversal argument. In each tile and buffer use the order H(δ) from Theorem 3.5. For a tuple of length θ, record its term labels, the fixed initial positions it uses, and, separately in each of the finitely many variable orders, the order and realized-cut record of its support positions. If θ < cf(δ), equal records are carried to one another by order automorphisms of the respective tiles and buffers. Their product fixes the initial data and induces an automorphism of the whole system. The set of possible records has a bound depending only on θ, the finite shape, and the template. Hence the system orbits at that arity have a uniform set bound.

Number these orbits and record the arrows between them, together with the partial map from support records to orbit names. This is again a bounded palette. If reversal fails unboundedly often, choose repeated profiles at eligible levels a < µ exactly as in Theorem 3.11, with$a^{θ} ≤$µ and the required large cofinalities for the orders. Apply the ordinal-position shrinking of Proposition 3.9 simultaneously to the finitely many tiles and buffers. Given at most a parameters in the large system, the resulting small presentation contains them, has size a in every tile and buffer, and computes the support records of all its θ-tuples correctly. Its inclusion is an actual arrow by Proposition 11.6. Thus it is an aligned small geometric system, not merely a componentwise subsystem.

For completeness, the contradiction uses two orbit names p, r with p → r and r ̸→ p. Repeatedly choose aligned small copies, each containing the previous one, and process their at most$a^{θ}$tuples in the large level. Whenever a tuple can still be sent to p, send it onward to r. From that point it cannot reach p. Coherence makes the successive small copies a chain of arrows. After$θ^{+}$rounds every θ-tuple of their union occurred at a proper round. Both unions exist by Lemma 11.5: the small union has total size a, and the large construction has total size µ. Alignment says that none of the tuples of the small union can reach p. Categoricity of that union at a says that its orbit p is realized, a contradiction. This proves eventual reversal at each fixed arity.

Mixed Löwenheim–Skolem closure also has the required form. In a presentation, close the supports of a prescribed small set under finitely many intermediate and exterior positions in every tile and buffer, repeat countably many times, and pad each order to the chosen smaller eligible size. The resulting dense endpoint-free suborders give a small presentation containing the set. The initial pointed order is retained in full. Its inclusion is an arrow by Proposition 11.6. Transport through a presentation of an arbitrary large object gives mixed containment; coherence supplies comparisons between such subobjects.

We now apply the first route of Proposition 5.8. Its structural hypothesis is Lemma 11.5; its presentation and mixed downward-closure hypotheses are Proposition 11.6 and the preceding paragraph. Categoricity is the input assumption, and the required arity-by-arity reversal and uniform orbit bounds were proved above. Thus the proposition applies to the actual system arrows, including their relative-basis condition.

In particular, the canonical comparison at a smaller input level is computed in a small geometric subobject. Two such sections are contained in a common small section by mixed downward closure, and coherence gives its arrows, so the comparison is well defined. The projections between comparisons at two input levels are onto because the smaller system is a tiled presentation and extends by the mixed order arrows of Proposition 11.6. The bounded palette therefore stabilizes, exactly as in the first route of Proposition 5.8.

Choose receiving levels which remain eligible, are strictly closed under the resulting arity bounds, and have sufficiently large smaller input levels below them for every bounded request. These are the closure refinements described in Section 5.2, supplied simultaneously in Theorem 13.5; closure under the next input level is not being used to infer eligibility by itself. At such a level, countable alternating matching in smaller input-level sections gives actual system isomorphisms on equal bounded diagrams, and realizes possible bounded joint diagrams over their given subtuples. Thus diagrams, homogeneity, and saturation have the system interpretation required here, rather than merely their componentwise K interpretation. Order embeddings and order amalgamation make the diagrams natural on term tuples, so Proposition 5.9 also applies.

It remains to check the additional exhaustion condition, which Proposition 5.8 explicitly leaves as a separate obligation. A finite tuple independent modulo the proper lower vertices stays so when its target diagram agrees with a tuple placed along an actual presentation arrow: the comparison is realized by a system isomorphism, and such an isomorphism preserves relative independence. Every tuple in an exhaustive sequence is handled at a stage containing it. The finite relative-independence criterion in Lemma 11.4 then supplies the additional arrow condition. Componentwise strongness is the conclusion of the same proposition’s exhaustion argument. This completes the working-package verification.

All refinements used here are the bounds for the original reversal, alignment, diagram stabilization, and saturation arguments, applied to finitely many orders and the fixed initial data. None introduces an amalgamation assumption on the original AEC; the amalgamation used below is the conclusion of the working package and Theorem 6.6.

## 11.4 Fresh coordinates and the two induction assertions

Fix pieces$(H_{s^{X}}: s ∈$L) in a system X. For an arrow X → Y, extend them to pieces

$H_{s^{Y}} = H_{s^{X}}$∪˙$C_{s^{Y}}.$

The sets$C_{s^{Y}}$are its complementary pieces. Their sizes may be any cardinals at most µ, including zero, even though all the total pieces have size µ.

Definition 11.8 (Joint freshness). A list of coordinates in an extension Y of X, with individual active labels, is jointly fresh over X if it is a sublist of the complementary pieces for some such extension of the pieces of X. At a single label s, the corresponding condition is independence over

cl$P (X_{s}) ∪ D_{s}$(Y).

For several labels these relative conditions assemble into joint freshness by Lemma 11.4. Coordinates are regarded as occurrences in their designated vertex sorts.

Freshness is preserved by arrows of extensions. Indeed every failure or success of finite independence over the displayed flat is determined by finite rank calculations using parameters from$P (X_{s})$and the lower span. The observation following Lemma 11.5 preserves those calculations. This also shows that freshness is an invariant of the type over X once the working package is available.

Theorem 11.9 (Classification with prescribed basis maps). For each finite admissible shape L, at all sufficiently closed uniform levels µ, the following assertions hold.

1. If X,$Y ∈ G_{L},$an isomorphism$e_{∅}: X_{∅} ≃ Y_{∅}$and arbitrary bijections between the chosen nonroot pieces of X and Y extend to a system isomorphism X ≃ Y. In particular$G_{L}$is categorical at these levels.

2. Suppose X → Y and X → Z are arrows in$G_{L}.$Choose pieces of X, extend them to pieces of Y and Z, and prescribe a bijection$C_{s^{Y}} ≃ C_{s^{Z}}$for every active label s. Then there is a system isomorphism$Y ≃_{X} Z$realizing every prescribed bijection. The complementary cardinalities may be less than µ, and zero is allowed.

The level requirements are uniform over the finitely many shapes at any fixed number of axes.

Proof. We prove the two assertions in order, by the number of axes. On no axes, the first assertion is exactly the assertion that a prescribed isomorphism of the root models is an isomorphism of the systems. Existence of such a root isomorphism, hence categoricity of the zero-axis scheme, is Proposition 10.6.

Suppose the second assertion is known for all shapes on fewer axes. For a shape with last-axis description L', apply the first assertion for L to its lower layers and then the second assertion for L to its upper layers. The pieces added at labels in Q are exactly the pieces bearing labels s ∪ {k} in L'. Prescribe their given bijections, and prescribe the empty maps at the other labels. This produces the desired isomorphism of the two-layer systems by Lemma 11.5. If an auxiliary root basis has been chosen, replace the target root basis by its image under the prescribed root isomorphism; Lemma 11.4 permits that replacement without changing any prescribed nonroot piece. Thus the first assertion at the next number of axes follows from the preceding second assertion.

It remains to prove the second assertion for a fixed shape L whose first assertion has now been established. Refine the levels using Proposition 11.7. All the one-dimensional calculus and dominated-hull results are then available for$G_{L}.$The rest of the proof is given in four claims.

Claim 11.10 (Uniqueness of finite fresh types). For a fixed base X and a finite ordered list of active labels, all jointly fresh tuples with those labels have the same type over X.

Proof. At zero axes this is the base-change calculation of Proposition 10.7. Types in the pointed scheme over a whole pointed base are the underlying K-types: an amalgam or type identification over that base already fixes the point. All objects at the level have full P-rank by Corollary 10.10.

At a positive number of axes suppose two finite jointly fresh tuples$b^{0}, b^{1}$have different types over X. Bounded testing gives a bounded tuple f from X such that

D(f,$b^{0})$̸= D(f,$b^{1}).$

Choose a cardinal χ < µ large enough for the orbit bound at arity |f |, for the finite tuple lengths, and for the template labels, with$χ^{|f|+ℵ_{0}} =$χ. Let ϵ be the least cardinal for which$2^{ϵ} >$χ. Then ϵ ≤ χ, there are at most χ nodes at all proper levels of the binary tree of height ϵ, and$2^{ϵ} ≤ 2^{χ} <$µ.

Build a tree of extensions of X at level µ. At a node V, the arrow from X preserves the diagram of f. Bounded-tuple homogeneity therefore supplies an isomorphism X ≃ V fixing f. Transport the two witness extensions along this isomorphism to form the children of V. Their marked tuples are fresh over V, and their diagrams with f have the two specified different values. At limit nodes take unions along the branch. Extend chosen basis pieces at every step. Hence along every branch all marked coordinates, at their respective labels, lie in complementary pieces over the initial X. The total size along a branch is µ, so all unions are allowed. Notice that the return isomorphism fixing f uses diagram homogeneity, not categoricity alone.

At every leaf make a further rich extension by Proposition 11.6, so that the root has complementary rank µ over the original$X_{∅}.$There is a common system U with the same property: present any system and make a rich extension, transporting it over X using categoricity. For each level η < ϵ reserve in U a finite tuple$c_{η}$of coordinates with the same labels as the marked tuple at that level. Choose all of these coordinates from complementary pieces over X. Their total number is at most χ.

For a leaf W, its root marked coordinates and those in U are independent over$P (X_{∅}).$Both full root complements have size µ, and the prescribed match uses fewer than µ coordinates. Extend that match to a bijection of root complements. The already proved second assertion for zero axes gives$W_{∅} ≃_{X_{∅}} U_{∅}$

carrying all root marked coordinates correctly. At nonroot labels extend the prescribed matches of marked coordinates to bijections of the full pieces, whose sizes are µ. The first assertion for the present shape extends these maps and the root isomorphism to an isomorphism W ≃ U. The old nonroot pieces of X need not be fixed in this step.

Let$f_{W}$be the image of f in U. Two different branches first separate at a level η; preservation of diagrams along their arrows gives different values of$D(f_{W}, c_{η})$after the two leaf isomorphisms. Thus the$2^{ϵ}$images of f lie in different orbits over the fixed set of at most χ reserved coordinates. The parameter-orbit bound of Lemma 6.1, applied to the working scheme, is χ at these arities, a contradiction.

For each active s, let$p_{s^{X}}$denote the unique fresh singleton type given by the claim. Such types exist by the rich extensions of Proposition 11.6 and categoricity. Their realizations lie outside the base vertex, so they are nonalgebraic.

Claim 11.11 (Free lifts preserve freshness). The free lift of$p_{s^{X}}$along an arrow X → V is fresh over V. Finite jointly fresh tuples have the product of their singleton types. Bounded jointly fresh lists have a unique whole type specified by their labels and admit all-dominated hulls.

Proof. Let a realize the free lift in an extension Y of V. If a is not fresh, finite character gives a finite tuple$c ⊆ P (V_{s})$with a ∈ cl$c ∪ D_{s}$(Y).

This condition is invariant under system isomorphisms and is therefore determined by the bounded diagram of (a, c) in Y. Its witnesses in lower vertices need not lie in V; the isomorphism-invariant condition itself is what the diagram records.

Put m = |c| + 1, and choose an m-tuple b jointly fresh over X, all at label s. Every singleton marginal is$p_{s^{X}}$by Claim 11.10. Take a sufficiently long bounded family of approximations, inside X, for tp(b/X), as in Lemma 6.9. By the support-copy construction in that Lemma, every approximating tuple has the same diagram as b without parameters, and is consequently independent modulo$D_{s}$(X). In the free lift to V, each coordinate has the same marginal as a. For each coordinate, the majority estimate gives the diagram of (a, c) outside a uniformly bounded set of approximation indices. Choose the family longer than the union of these finitely many exceptional sets. One approximating tuple$(a_{1},..., a_{m})$is independent modulo$D_{s}$(X) and has, coordinate by coordinate, the required diagram with c in V.

Since X → V is an arrow, this tuple remains independent modulo$D_{s}$(V). The comparison just obtained is an equality of$G_{L}$-diagrams,

$D_{G_{L}}$(a, c; Y)$= D_{G_{L}} (a_{i},$c; V).

The established working package therefore gives a system isomorphism$F_{i}: Y ≃ V$taking a to$a_{i}$and fixing the displayed tuple c. It carries every lower vertex onto its counterpart and preserves the pointed closure, so$F_{i} [D_{s}$(Y)]$= D_{s}$(V). Transporting the dependence witness gives$a_{i} ∈$cl(c$∪ D_{s}$(V)) for every i. The latter flat has relative rank at most |c|, whereas the tuple has relative rank m > |c|. This contradiction proves that the free lift is fresh.

Realize a finite product successively by free lifts along a chain of extensions. The assertion just proved puts each new coordinate in a complementary piece over the preceding system. Extending pieces along the chain makes the whole tuple jointly fresh over X. Claim 11.10 then says that every jointly fresh finite tuple has this product type. A bounded jointly fresh list is consequently product-independent in the sense of Theorem 7.13. That theorem gives its unique whole type and its witnessing free chains; its all-dominated-hull conclusion gives existence over the list.

We now know the types of fresh coordinate lists and have all-dominated hulls over them. To extend a partially prescribed basis map, we also need to cover an arbitrary bounded tuple using only boundedly many new coordinates. The next claim provides this size control, including when the target basis has already been chosen.

Claim 11.12 (Bounded rank cost and chosen coordinates). Let X → Y be an arrow. A finite tuple d of Y is contained in a subextension X → U → Y whose complementary pieces have finite sizes. For an arbitrary bounded tuple d, their sizes can be bounded by max(|d|,$ℵ_{0}).$

If specified pieces of Y extend those of X, the subextension containing a bounded d can be chosen with all its complementary pieces subsets of the specified complementary pieces of Y, still of bounded total size.

Proof. For finite d, take an all-dominated object over X + d and embed it into Y by Proposition 7.5. Call its image U. Suppose one complementary piece of U is infinite. Choose a sequence$(a_{i}: i <$ω) from that piece. It is jointly fresh and hence product-independent over X. The witnessing-chain assertion of Theorem 7.13 retains this configuration in a chain

$X = V_{0} −→ V_{1} −→ · · · −→ V_{ω},$

where$a_{i}$is free over$V_{i}$from X and belongs to$V_{i+1}.$We may construct this chain inside the actual U. At each stage, finite domination makes the actual next coordinate$a_{i}$free over$V_{i}$from X, since its products with the preceding coordinates remain those of the original list. Choose an all-dominated increment over$V_{i} + a_{i}$and use primeness to embed it into U, fixing this base and this coordinate. At limits take unions inside U, using the common-upper-bound clause. Thus$V_{ω} ≤$U, and the tuple d and every$a_{i}$retain their actual positions in U. Equivalently, the witnessing-chain amalgamation may retain all of these data in a common extension.

The tuple d is finite, so Proposition 6.13 at the limit of cofinality ω makes the actual type$tp(d/V_{ω};$U) free from some$V_{n}.$Hence d and$a_{n}$have product over$V_{n}.$The base-change rule of

Proposition 6.12, together with the freeness of$a_{n}$over$V_{n}$from X, gives that$a_{n}$and d have product over X. Domination of U over X + d now makes$tp(a_{n}$/U) free from X. This is impossible by Claim 11.11: the free lift of its fresh singleton marginal must be fresh over U, whereas$a_{n} ∈ P (U_{s}).$Therefore every complementary piece of U is finite.

For a bounded list of cardinality τ, include its entries successively by this finite construction, with the preceding subextension as base, and take unions at limit stages. There are finitely many labels. At most τ finite increments therefore add at most κ = max(τ,$ℵ_{0}) <$µ coordinates in total. All objects continue to have size µ, and their unions have total size µ. This proves the bounded version.

For the final assertion fix the target partition$H_{s^{X}}$∪˙$C_{s^{Y}}.$Starting with a bounded-rank subextension containing d, repeat the following construction countably many times. Choose relative bases for the current subextension over X. Each gained basis element in vertex t has a finite support in the fixed target basis, consisting of old coordinates and coordinates of$C_{s^{Y}}$with s ⊆ t. Request all the latter supporting coordinates in their own vertices, and include them in the next subextension using the bounded construction just proved. At every step at most κ coordinates are requested and the total new rank remains at most κ.

In the union let$C_{s}$consist of the requested coordinates of label s. These sets are independent, together with the pieces of X, because they are subsets of the target partition. They span every union vertex over its old pieces: an element occurs at a stage, is spanned there by the gained pieces and the old pieces, and the finite target supports of those gained pieces were requested at the next stage. Conversely the closed P-set of each union vertex contains all the indicated coordinates below its label. Thus the span identities hold in both directions. The$C_{s}$are precisely complementary pieces of the union, have total size at most κ, and are subsets of the prescribed$C_{s^{Y}}.$

Claim 11.13 (Primeness over bounded complementary pieces). If X → U has a bounded list b enumerating all its complementary pieces, then U is all-dominated over X + b. It embeds over X into any extension realizing a prescribed matching of these coordinates.

Proof. The list b is product-independent by Claim 11.11. Take an all-dominated object over X + b and embed it into U over these data. Its image V contains in each vertex the old P-set and all the complementary coordinates with labels below that vertex. Relative closedness and the span identity imply$P (V_{t}) = P (U_{t})$for every t. The no-proper-pair conclusion then gives$V_{t} = U_{t}$for every vertex. Thus V = U, proving the domination assertion.

A prescribed matching of b into another extension gives the same whole type over X, by Claim 11.11. Primeness of the all-dominated object therefore gives the desired arrow fixing X and realizing that matching.

We finish the second assertion of the theorem. Identify the two bases with X, and keep the prescribed bijections of all complementary pieces. Choose countable exhaustions of the two targets by bounded lists; these exist because the eligible level µ has cofinality ω and there are only finitely many vertex sorts. Construct alternating isomorphisms between subextensions of the two targets. Initially use$id_{X}.$Maintain the invariant that the complementary pieces in each current subextension are subsets of the specified target pieces, and that the current isomorphism agrees with their prescribed bijections.

At a forth step, apply Claim 11.12 over the current subextension on the first side to include the next bounded list and to use only remaining specified coordinates. Its new complementary list is bounded. The corresponding coordinates on the second side are jointly fresh over its current subextension. Claim 11.13, transported by the current isomorphism, embeds the enlarged subextension into the second target over that isomorphism and realizes their prescribed matching. Its image is the next subextension there. The span identities show that its complementary pieces are exactly the specified images of the new pieces, so the invariant is preserved. A back step applies the same construction with the roles interchanged.

The union of these countably many coherent isomorphisms covers both targets, since every list in both exhaustions is eventually included. It is therefore a system isomorphism over X. It realizes all prescribed basis bijections: every basis element is eventually in the domain, and the invariant determines its image. This proves the second assertion, with no lower bound on complementary cardinalities.

The induction is complete. At each fixed finite number of axes there are only finitely many active-label families. Taking the maximum of their finitely many bounds gives the stated uniformity. Simultaneous closure through all finite numbers of axes is addressed separately in Theorem 13.5.
