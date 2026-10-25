# 14 Transfer to all larger cardinals


The common levels of Theorem 13.5 provide one cardinal at which all finite geometric shapes have exact boundary lifting. This section uses that single cardinal as the base of an induction through the cardinals. The levels supplied by the closure construction themselves need not contain a tail.

The trade between one extra dimension and an increase in cardinality goes back to Shelah’s multidimensional existence and uniqueness methods [She83, Theorems 5.1–5.2]; compare their later formulation in [SV24, Lemma 11.6]. The argument below is given for the exact boundary maps and cardinal assignments used here.

Fix a common uniform level γ from Theorem 13.5, for all the geometric shapes and their exact boundary assertions. Choose it strictly above the no-growth threshold λ of Corollary 10.10, and above all fixed point and single-model thresholds. In particular$γ > λ_{0},$the cardinality of the distinguished model$M_{0}.$In every pointed model of cardinality at least γ, model cardinality equals the cardinality of a basis of its point geometry.

Definition 14.1 (Prescribed piece cardinalities). Let L be an allowed family on a finite axis set a. A cardinal assignment on L is a family of cardinals

$(κ_{s}: s ∈$L),$γ ≤ κ_{s} ≤ κ_{t}$(s ⊆ t in L).

A system with this assignment satisfies the span and inclusion conditions of Definition 11.1, with a witnessing basis partition$(H_{s}: s ∈$L) such that$|H_{s} | = κ_{s}.$The bases are not named. A prescribed boundary isomorphism has the meaning of Definition 12.1.

For t ⊆ a let$a_{L}$(t) be its largest active subset. The span identities and monotonicity imply

rk$P (X_{t}) = max{κ_{s}: s ∈$L, s ⊆ t}$= κ_{a_{L}}$(t). (16)

All these ranks are at least γ, so Corollary 10.10 shows that the same formula gives$∥X_{t} ∥.$It also shows that an inactive vertex equals$X_{a_{L}}$(t). Lemma 11.4 applies without a uniform-cardinality requirement: its proof only uses the finite shape and the basis axioms of the pregeometry.

Lemma 14.2 (Choosing subcubes with prescribed supports). Suppose two systems$X^{−}$and$X^{+}$have the same cardinal assignment, and prescribed isomorphisms$h_{t}$on their proper faces. Suppose their top is active and put

$κ = max_{s∈L} κ_{s}, Q =${s ∈ L:$κ_{s} =$κ}.

One can choose witnessing global basis partitions$(H_{s^{−}})$and$(H_{s^{+}})$such that

$h_{s} [H_{s^{−}}] = H_{s^{+}}$(s ∈ L, s ⊊ a). (17)

Fix such partitions. Let χ be a cardinal with γ ≤ χ < κ which bounds all$κ_{s} <$κ. Given at most χ requested elements in the finitely many vertices on both sides, there are subsystems$U^{±}$inside$X^{±}$with the following properties:

1. Each requested element belongs to its indicated vertex. Every vertex whose size is strictly below κ is retained in full.

2. Their witnessing pieces are subsets$I_{s^{±}} ⊆ H_{s^{±}}.$They equal$H_{s^{±}}$when s ∈/ Q, and have cardinality χ when s ∈ Q.

3. On every proper face,$h_{t} [U_{t^{−}}] = U_{t^{+}}.$

If compatible subsystems have already been chosen whose witnessing pieces are subsets of these fixed partitions$(H_{s^{±}}),$and whose total vertex sizes are at most χ, their entire vertices can be included among the requests. Moreover, at every s ∈ Q one can require exactly χ additional basis coordinates beyond those old selected pieces, on both sides. All resulting inclusions preserve the relative independence condition for system arrows.

Proof. Choose the pieces on the minus side. For each proper active s, the isomorphism$h_{s}$takes its lower span onto the corresponding lower span on the plus side, since it agrees with the prescribed maps on every lower vertex. Thus$h_{s} [H_{s^{−}}]$is a relative basis at s. By Lemma 11.4, these relative bases assemble in the plus system. Complete them by a relative basis at its top. Their cardinalities have the required values because relative rank is invariant under isomorphism. This gives the claimed partitions.

We construct the desired subsystems by a countable closure process, on both sides and at all the finitely many vertices. Begin with the requested sets, the fixed point, and any specified old subsystems. At every growing active label s ∈ Q, also request χ basis coordinates. In the extension version choose these outside the old selected piece. There are enough coordinates since$|H_{s^{±}} | = κ$and the old piece has size at most χ < κ. At a proper label the choices may first be made on the minus side and transported by$h_{s};$these are still fresh on the plus side. At the top make the choices on both sides separately. Retain all nongrowing vertices in full.

At each finite stage choose, by the Löwenheim–Skolem axiom, strong submodels of the ambient vertices containing all requests so far. Their sizes are at most χ: the LS bound, point, retained smaller vertices, and requested data all fit within that cardinal. At the next stage make the following further requests.

1. For each inclusion of labels s ⊆ t, put all elements of the currently chosen model at s into the requests at t.

2. For every point obtained in a chosen vertex, choose a finite support for it from the union of the global basis pieces below that vertex. Request each supporting coordinate in the vertex of its own active label.

3. At each proper face, request the image under$h_{t}$of every element currently included on the minus side, and the inverse image of every element currently included on the plus side.

Also retain all previous requests and chosen models. These operations make at most χ requests at each stage. Each ambient point set has the given basis partition, so the supports in the second operation exist and lie in the indicated vertices. For a retained smaller vertex all supporting labels are retained as well: if s ⊆ t and$κ_{t} <$κ, monotonicity gives$κ_{s} <$κ. Thus no operation requires enlarging a retained vertex beyond its given ambient model.

Take the unions of the chosen models through the countable process. Coherence makes all successive and vertex inclusions strong, and the AEC chain axioms give strong limit models$U_{t^{±}} ≤_{K} X_{t^{±}}.$On a proper face the image and inverse-image requests give exactly$h_{t} [U_{t^{−}}] = U_{t^{+}}.$This construction used the maps one face at a time; it did not assume that their union on possible extra intersections was already a function.

Put$I_{s^{±}} = H_{s^{±}}$∩P$(U_{s^{±}}).$Every point of$P (U_{t^{±}})$occurs in a finite-stage model, and its supporting coordinates were subsequently placed at their own labels. Conversely, the point set of$U_{t^{±}}$is relatively closed in the ambient model and contains all selected coordinates below t. Therefore

()

$P (U_{t^{±}}) =$cl (s∈L,⋃s⊆t$I_{s^{±}}).$

The selected pieces are subsets of the single global independent basis and hence are independent together. They supply precisely the required decomposition. Nongrowing pieces and vertices were retained in full. At a growing label at least χ coordinates were requested and its model has size at most χ, so its piece has size exactly χ. In the extension version, at least χ fresh coordinates were requested; at most χ coordinates altogether were added. The additional piece therefore has cardinality exactly χ.

Finally, the selected subsets increase when old subsystems are included. Being subsets of the same global basis proves the relative independence requirement for their inclusions, using the criterion of Lemma 11.4.

The subcube lemma makes compatible smaller systems available, but an arbitrary isomorphism between the next two subcubes need not extend the previous one. The cardinal induction resolves this by adding an axis: the old full isomorphism becomes part of a boundary prescription at a strictly smaller maximum cardinal. This is why the induction must cover all finite shapes simultaneously.

Theorem 14.3 (Exact lifting at every larger cardinal). For every finite allowed shape and every monotone assignment$(κ_{s}: s ∈$L) of cardinals at least γ, any prescribed boundary isomorphism between two systems with that assignment extends to an isomorphism of their tops.

Proof. We induct on the cardinal$κ = max_{s∈L} κ_{s},$proving the assertion simultaneously for all finite shapes and all assignments with that maximum. For κ = γ all pieces have size γ, so Theorem 12.2 applies at the chosen common level. Suppose κ > γ and the assertion is known at every smaller maximum.

As before, an inactive top equals a proper active vertex and its prescribed map already gives the conclusion. Assume the top is active. Keep all smaller pieces and their vertices in full. There are only finitely many of them, so their cardinalities have a common bound below κ. Choose the global basis partitions of Lemma 14.2.

Let δ = cf(κ). Choose an increasing sequence$(α_{i}: i <$δ) of ordinals below κ, cofinal in κ, and fix enumerations of every growing vertex on each side by κ. We construct continuous chains of subsystems$(U_{i^{−}}: i <$δ),$(U_{i^{+}}: i <$δ),

and compatible full system isomorphisms$f_{i}: U_{i^{−}} ≃ U_{i^{+}}.$Every proper-face restriction of$f_{i}$is the given$h_{t}$on that subface. Their pieces are increasing subsets of the chosen global partitions.

Nongrowing vertices are retained in full; all growing pieces at stage i have the same cardinality$ρ_{i} <$κ, at least γ.

For the initial stage, choose χ < κ bounding γ, the retained pieces, and the sizes of the requested initial enumeration segments. Apply Lemma 14.2 on both sides. This gives systems with the same piece sizes and maximum below κ, whose proper-face maps are the restrictions of the given prescription. The induction hypothesis at that maximum supplies$f_{0}.$

Suppose$U_{i^{±}}$and$f_{i}$are given. Choose a cardinal χ < κ which bounds γ, all retained piece sizes, all old vertex sizes, and the next requested enumeration segments. The size checks justifying this choice at every proper stage are given below. Apply the extension part of Lemma 14.2. It produces$U_{i+1^{±}}$containing the old systems and the requested segments, with exactly χ new independent coordinates at every label in Q = {s ∈ L:$κ_{s} =$κ},

and none at the other labels. The set Q is upward closed: if s ∈ Q and s ⊆ t ∈ L, then$κ ≤ κ_{t} ≤$κ, so t ∈ Q.

Add a new last axis k. Regard$U_{i^{±}} → U_{i+1^{±}}$as the two layers of systems with active labels

L' = L ∪ {s ∪ {k}: s ∈ Q}.

The old pieces have their previous cardinalities and the additional pieces all have cardinality χ. These are valid decompositions: the old and added coordinate sets are disjoint subsets of the fixed global basis, and their unions span the new vertices. The cardinal assignment on L' is monotone. Comparisons among old labels use the old monotonicity, comparisons among new labels use equality to χ, and an old label below a new one has size at most χ by its choice. No new label is contained in an old one. All assigned cardinals are at least γ and the maximum is still strictly below κ.

Prescribe the boundary maps of these enlarged shapes by$f_{i}$on the entire old cube and by the given$h_{t}$on every enlarged proper face of the new cube. They commute on all indicated subfaces: on an old proper face the two prescriptions already agree by the invariant for$f_{i}.$The cardinal induction hypothesis applies to this shape as well, since it is simultaneous in the number of axes and its maximum decreased. It yields an isomorphism of the new tops extending$f_{i}$and all the enlarged proper-face maps. This is the required$f_{i+1}.$

S

coherent,At a nonzeroso$f_{i}$is limitan ontoi <isomorphismδ, take componentwisebetween theseunionsunions,andwithput$itsf_{i}$=requiredj<i$f_{j}$face. Therestrictions.maps are

The component unions are strong submodels of the actual ambient vertices by the AEC common-upper-bound axiom. Union pieces are still independent by finite character. Every point in a union vertex occurs at some stage and has a finite support in that stage’s selected pieces, so the union pieces span. These are thus systems of the required shape, and inclusions continue to preserve relative independence.

Here are the cardinal calculations at proper stages. If$κ = τ^{+}$is a successor cardinal, choose χ = τ at the initial and every growth stage. Every proper stage index has cardinality at most τ, and every union at such a stage has size at most τ · τ = τ. The enumeration segments below κ also have size at most τ. Hence every stated choice and every proper-stage induction application has maximum strictly below κ.

If κ is a regular limit cardinal, there are fewer than κ earlier stages at every i < δ = κ. Regularity bounds their sizes and their union by a cardinal below κ. Enlarge the next χ to cover that bound, the finitely many retained sizes, and the next enumeration segments. It can still be chosen below the limit cardinal κ, and may be increased cofinally through κ.

If κ is singular, at a proper stage i < δ fewer than cf(κ) earlier cardinals have been used. Their supremum is therefore below κ. Both that supremum and |i| have a common cardinal bound below κ, as do the finitely many retained sizes and the next enumeration segments. Their maximum bounds the union and can be used in choosing χ. In particular this argument applies when cf(κ)$= ℵ_{0};$the final countable union has size κ, while every proper stage remains below it.

The variable pieces have equal sizes on the two sides and at all growing labels. This is immediate initially and at successors, where the same additional cardinal χ is used everywhere. At a limit their sizes are the same cardinal sum of the initial piece and the previously added disjoint pieces. The preceding bounds keep that sum below κ at a proper stage. Monotonicity also persists, since the smaller retained pieces were bounded by the initial variable size.

Finally take the unions over i < δ. The requested enumeration segments are cofinal, so these unions are the two original systems. The union of the$f_{i}$is an onto isomorphism of the tops with every prescribed restriction. The final union is allowed to have cardinality κ; the induction hypothesis was used only at proper stages, where the maximum was smaller. This completes the cardinal induction.

Corollary 14.4 (Pointed categoricity on a tail). For every cardinal κ ≥ γ, any two models of cardinality κ carrying the fixed point pattern are pointedly isomorphic.

Proof. On zero axes the only active piece is a basis of the whole point geometry. Its size is the model cardinality by Corollary 10.10. Apply Theorem 14.3 with the one-element cardinal assignment κ. The boundary is empty.

Theorem 14.5 (Categoricity on a tail). If an AEC K is categorical in unboundedly many cardinals, then there is a cardinal θ such that K is categorical in every cardinal κ ≥ θ. Here categoricity includes the existence of a model at each such cardinal.

Proof. All preceding constructions were made for this fixed AEC under the hypothesis of unbounded categoricity. Choose γ as above. Fix a sufficiently large categorical cardinal ρ ≥ γ at which a pointed presentation with the chosen diagram of$M_{0}$exists and the stabilized K-diagrams on its enumeration are preserved by strong maps into larger models. Such a ρ is available from the single-model working levels and Proposition 10.6. We may take θ = ρ.

Let M be any model of cardinality κ ≥ ρ. Choose a subset of its universe of cardinality ρ. The LS axiom gives a strong submodel$N ≤_{K} M$containing that subset and of size at most ρ + LS(K) = ρ. Thus ∥N ∥ = ρ exactly. Categoricity in ρ identifies N with the pointed presentation just chosen. Transport its copy of$M_{0}$into N and then into M. The fixed diagram on its whole enumeration is preserved by the strong inclusion, so M has the required point pattern. Notice that this uses categoricity at the fixed smaller cardinal ρ, not a categoricity assertion at κ.

Consequently any two models of cardinality κ ≥ θ can be given the chosen point pattern. Corollary 14.4 identifies them pointedly, and forgetting that point gives a K-isomorphism. This proves uniqueness.

For existence, take a linear order I of cardinality κ. The order presentation of Theorem 2.6 is a member of K and has size exactly κ: its distinct skeleton gives the lower bound, and its at-most-LS(K) labels on finite lists give the upper bound κ + LS(K) = κ. Hence there is exactly one isomorphism type, rather than merely at most one, at every cardinal in the asserted tail.

Conclusion of the uniform theorem

Proof of Theorems 1.3 and 1.2. Theorem 14.5 proves the qualitative assertion of Theorem 1.3. Apply the set-coding reduction of Proposition 2.3 at a fixed infinite LS bound λ. For each of its set-many AEC codes, either the categoricity spectrum is bounded, or the qualitative assertion gives categoricity on a tail. In the bounded case choose a strict upper bound for every categorical cardinal of that code. In the unbounded case choose a threshold for its categorical tail. Replacement over the set of codes gives a common cardinal bound µ(λ) ≥ λ above all these choices.

If an AEC with LS number at most λ is categorical at any cardinal κ ≥ µ(λ), its code cannot be one of the bounded-spectrum cases. Its categorical tail therefore contains every κ' ≥ µ(λ). This is exactly Theorem 1.2, with the same threshold in its premise and conclusion. No regularity, successor, amalgamation, or no-maximal-model hypothesis has been added to the statement.
