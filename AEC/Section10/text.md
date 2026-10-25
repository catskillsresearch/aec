# 10 A minimal type and its geometry


We continue with the fixed AEC K that is categorical in unboundedly many cardinals. Throughout this Section, a level is eligible for the single-model working scheme and for the refinements of the calculus that are explicitly invoked. The first level chosen below is denoted by$λ_{0}.$The level used for all finite marked constructions will be a later cardinal λ; these two choices serve different purposes.

Lemma 10.1 (Preservation of nonalgebraicity). Let p be a nonalgebraic singleton type over an object A of a working scheme. Its free lift over an extension B is nonalgebraic. The same assertion holds for a mixed arrow whenever the input arity and the testing bounds lie below the smaller level.

Proof. Suppose that the free lift were realized by c ∈ B. Include equality with c among its tests. To evaluate that test, the free-extension construction moves c into A, over enough of the chosen approximations for p. Its value is then the value of equality with an element of A. Every such equality has value false for p, whereas equality with its alleged realization c has value true. This contradicts the evaluation rule in Theorem 6.10. The mixed-level construction uses the same rule with the bounds taken below the input level.

Proposition 10.2 (A minimal type). There is a sufficiently closed single-model level$λ_{0}, a$model$M_{0} ∈ K$of size$λ_{0},$and a nonalgebraic singleton type$p_{0}$over$M_{0}$such that, over every$M_{0} ≤_{K} A ∈ K$of size$λ_{0},$there is exactly one nonalgebraic extension of$p_{0}.$This extension is its free lift.

Proof. Choose$λ_{0}$with the single-model working package, the stationary calculus, the all-dominated hull construction, and the singleton type bound of Theorem 4.11(3). Thus there are at most$λ_{0}$singleton types over a model of that size. We may require at the outset strict closure under all the fixed bounds used below for finite tuples and their bounded tests.

There is a nonalgebraic singleton type at this level. For example, extend an order presentation by a fresh skeleton point. That point is outside the old model: if it were a labeled term on finitely many old indices, adding a second distinct skeleton point with the same order pattern over those indices would make both equal that term, contrary to the distinctness of the skeleton.

Suppose that no nonalgebraic singleton type at this level is minimal in the stated sense. A nonalgebraic type always has a nonalgebraic free extension by Lemma 10.1. Consequently every such type has two distinct nonalgebraic extensions over some model of size$λ_{0}.$

Let ϵ be the least infinite cardinal with$2^{ϵ} > λ_{0}.$Then ϵ$≤ λ_{0}$and$2^{|i|} ≤ λ_{0}$for i < ϵ. Construct i

a continuous chain$(A_{i}: i ≤$ϵ) of models of size$λ_{0}$and types$p_{η}$over$A_{i},$for η ∈ 2, as follows.

At a successor step, split every current$p_{η}$over a model extending$A_{i}.$There are at most$λ_{0}$such models. Successive amalgamation over$A_{i},$followed by unions, puts all of them into one next base$A_{i+1}$of size$λ_{0}.$Freely extend each of the two split types to that base. Their restrictions to the splitting model are different, so they remain different, and Lemma 10.1 keeps them nonalgebraic.

Along each branch retain a witness model and the same distinguished realization. The required successor map exists by amalgamation with identification of realizations having the same type over the preceding base. At a limit take the unions of the common bases and, separately on each branch, of its coherent witness models. The realization is outside every base stage, so it is outside the union base. All these unions have size$λ_{0}$because the construction has length at most$λ_{0}.$At the final stage distinct branches have different types over$A_{ϵ},$witnessed at their first splitting stage. This gives more than$λ_{0}$singleton types over$A_{ϵ},$contrary to the type bound. A minimal$p_{0}$therefore exists. Its unique nonalgebraic extensions are free by existence of free lifts.

The passage from a minimal type to closure and dimension follows the geometric pattern of first-order categoricity developed through strongly minimal sets; see Baldwin and Lachlan [BL71, Sections 1–2]. Here the required containment, exchange, and change-of-base properties are established directly for the AEC and its locally constructed types.

## 10.1 Finite configurations over the chosen model

Definition 10.3. For$M_{0} ≤_{K} M$with ∥M$∥ ≥ λ_{0},$let P (M) be the set of realizations of$p_{0}$in M. More explicitly, a ∈ P (M) means that in a strong section$N ≤_{K} M$of size$λ_{0}$containing$M_{0} ∪${a}, the type$tp(a/M_{0})$is$p_{0}. A$finite ordered list of distinct points in P (M) is independent if its type over$M_{0},$computed in such a section, is the product of the corresponding copies of$p_{0}.$

These definitions do not depend on the section. Two sections lie in a third section of size$λ_{0},$by the Löwenheim–Skolem axiom and coherence. The embeddings into that section preserve their types over$M_{0}.$Products are permutation invariant, so independence is a property of the underlying finite set. Strong embeddings over$M_{0}$preserve and reflect both membership in P and finite independence.

We give a precise meaning to the containment test used in constructing closure. Fix a finite configuration F ∪ {x} ⊆ P (M) and$a size-λ_{0}$section N containing it and$M_{0}.$Say that F forces x if, whenever f: N → W is a strong embedding fixing$M_{0},$with W of size$λ_{0},$and$M_{0} ≤_{K} D ≤_{K} W$has size$λ_{0}$and contains f [F], one has f (x) ∈ D. Thus the test permits a common extension of the finite configuration and the proposed model; it does not presume that intersections of strong models are strong models.

The test is invariant under the type of the entire finite configuration over$M_{0}.$Indeed, an identification of two copies of that type is witnessed in an amalgam. Any further configuration witnessing failure of forced containment can be amalgamated with that identification over the first witness model. Its avoiding submodel and the omitted point remain disjoint at that point because the maps are injective. This transports the failure to the second copy. The reverse transport is identical with the copies interchanged.

Lemma 10.4 (The containment test). For a finite independent set S ⊆ P (M) and x ∈ P (M), S fails to force x if and only if S ∪ {x} is independent with x ∈/ S.

Proof. First suppose that a coupling contains a model D over$M_{0}$and S but omits x. The type of x over D is a nonalgebraic extension of$p_{0}.$By Proposition 10.2 it is the free lift of$p_{0}.$Restricting its parameters to S shows, by Proposition 6.12, that x has product type with S over$M_{0}.$

Conversely suppose that S, x has product type. Use Theorem 7.9 to obtain a model all-dominated over$M_{0} +$S, and amalgamate it with the actual finite configuration, identifying the copy of S. The domination conclusion of Proposition 7.5 makes x free over this model from$M_{0}.$It is outside the model by Lemma 10.1. The same amalgamation can retain any further specified finite entries of the original configuration. This is a coupling witnessing that S does not force x.

Theorem 10.5 (The geometry of the minimal type). On P (M), for every$M_{0} ≤_{K} M$of size at least$λ_{0},$the preceding finite independence is the independence relation of a finitary pregeometry. Its closure, denoted by$cl_{M},$has the following properties.

1. For finite F ⊆ P (M) and any maximal independent S ⊆ F, the set$cl_{M}$(F) consists exactly of those points that do not independently extend S. Equivalently,$cl_{M}$(F) is the set of points forced by F.

2. Strong embeddings over$M_{0}$preserve and reflect finite closure. If$M_{0} ≤_{K} A ≤_{K}$M, then P (A) is relatively closed in P (M).

3. For finite F,$| cl_{M}$(F)|$≤ λ_{0}.$For every infinite F ⊆ P (M),

$| cl_{M}$(F)| ≤ |F$| + λ_{0}.$

In particular bases exist, all bases have the same cardinality, and each point of the span of a basis has finite basis support.

Proof. Choose a maximal independent subset S of a finite F. Every y ∈ F \S fails to independently extend S, so Lemma 10.4 says that every model containing S in the actual configuration must contain all of F. A point that fails to independently extend S is therefore forced by F. If x independently extends S, the avoiding dominated model from Lemma 10.4 can be adjoined while retaining F, x. It contains F by the preceding observation and omits x. Thus F does not force x. This proves the first assertion and its independence of the choice of S.

Define closure on arbitrary subsets by taking the union of closures of finite subsets. Extensivity and monotonicity hold directly from the containment test. To verify idempotence on finite configurations, suppose that finitely many$y_{j}$are in$cl_{M}$(F) and that x independently extends a maximal independent S ⊆ F. The avoiding model over S can be coupled with the whole finite configuration F,$(y_{j}),$x. It contains F and every$y_{j},$because all these points are forced by S, and it omits x. Hence the$y_{j}$cannot force x. Finite character now yields idempotence for all subsets.

For exchange, it suffices by finite character to take finite F and points x, y with

$y ∈ cl_{M}$(F ∪ {x}) \$cl_{M}$(F).

If$x ∈ cl_{M}$(F), idempotence would imply$y ∈ cl_{M}$(F), so x ∈/$cl_{M}$(F). Let S be a maximal independent subset of F. Then S, x and S, y are independent. Since every member of F is already forced by S, the set S ∪ {x} is maximal independent in F ∪ {x}. The displayed membership says that S, x, y is dependent. Permutation invariance of products makes S, y, x dependent as well. Applying the first assertion with S ∪ {y} gives$x ∈ cl_{M}$(F ∪ {y}). This is exchange.

Preservation and reflection follow from the invariant finite-type definition and the containment test. For relative closedness, take finite F ⊆ P (A) and$x ∈ cl_{M}$(F). Choose$D ≤_{K} A$of size$λ_{0}$containing$M_{0} ∪$F, and then choose a section of M containing D ∪ {x}. Forced containment gives x ∈ D ⊆ A. The finite closure of F lies in this same D, proving the finite cardinal bound. There are |F | finite subsets of an infinite F, so finite character proves the displayed bound.

For completeness, a maximal independent subset of a set can be constructed by well-ordering it and retaining a point precisely when it is outside the span of the points retained earlier. Finite character makes the resulting set independent, and maximality makes it spanning. If an independent set is spanned by a finite set of n points, it has at most n points: successively insert its points into a spanning list, using exchange to remove one of the original points whenever a new independent point is inserted. After n insertions no further independent point is in the span. This also proves equality of finite basis sizes.

For infinite bases H, J of the same closed set, choose for each j ∈ J a finite support$S_{j} ⊆$H.

S

Thencannotcl(J)belong⊆$cl(^{S_{j∈J}}to$the$spanS_{j}).$ofIndependencethe other members.of H impliesHence H|H|⊆≤ |J|;j∈J$interchangingS_{j},$because athememberbases ofgivesH

the reverse inequality. The finite argument excludes the possibility of one basis finite and the other infinite. Finally, for a closed C, the operator U 7→ cl(C ∪ U) \ C on P (M) \ C satisfies the same closure and exchange axioms. Finite character follows by discarding all but the finitely many entries of U in a dependence witness. Applying the preceding constructions to this operator gives relative bases and their finite supports.

## 10.2 Pointed levels and change of base

Choose an enumeration$m̄_{0}$of$M_{0}$and place it as a strong model in a sufficiently large well-ordered presentation of K. Such a placement exists by the order construction and categoricity at$λ_{0}.$Fix the stabilized diagram ∆ of this entire enumeration. The initial supporting positions of this placement will be held fixed in later order presentations.

Proposition 10.6 (Pointed working levels). At all sufficiently closed levels µ above the bounds for$|m̄_{0} | = λ_{0},$models with a distinguished strong copy of$M_{0}$whose enumeration has diagram ∆ form a categorical working scheme. Arrows preserve the indicated copy pointwise. For a pointed model B at such a level,$p_{0}$has a unique nonalgebraic extension$p^{B}$over B; it is its free lift. This family lifts freely along pointed arrows, including the permitted mixed arrows. Naming further bounded data of a fixed diagram within the base does not change type computation over the whole base.

Proof. The enumeration is a bounded tuple at µ. Bounded-diagram homogeneity in Proposition 4.3 carries it between any two instances of ∆ by an isomorphism of the entire models. The pointed version of the working package follows by reserving its supporting positions and including the enumeration in every relevant diagram, as in Proposition 5.7.

Existence of$p^{B}$is mixed free extension of$p_{0},$and Lemma 10.1 gives nonalgebraicity. To prove uniqueness, take two nonalgebraic extensions over B. A distinguishing test for singleton types may be chosen with a fixed bound below$λ_{0}.$For any such parameter set Z ⊆ B, choose$M_{0} ≤_{K} A ≤_{K} B$of size$λ_{0}$containing Z. Both types restrict to nonalgebraic extensions of$p_{0}$over A and are equal there by Proposition 10.2. Their diagrams on Z are consequently equal. The bounded testing theorem gives equality over B. Uniqueness and transitivity of free extension prove the assertion for pointed arrows.

All distinguished data here already belong to the parameter model. An amalgam over that model fixes them, and an identification of types over that model respects them. Thus adding them as constants does not change this type computation.

Proposition 10.7 (Change of base for the geometry). Let B be a pointed model at a sufficiently closed level much larger than$λ_{0}. A$finite list of points in an extension of B is independent over the closed set P (B) in the geometry of Theorem 10.5 if and only if its type over B is the product of the corresponding copies of$p^{B}.$

Proof. A product can be witnessed by successive free realizations in models containing all preceding entries. Each realization is outside that model by Lemma 10.1. Its point set is relatively closed, so the realization is outside the geometric span of P (B) and the earlier entries. This proves one implication.

For the converse let x be a finite list independent over P (B). Fix a parameter test Z ⊆ B large enough to be used in the uniform comparison of the type of x over B, but with |Z|$< λ_{0}.$Choose a regular infinite$θ < λ_{0}$with |Z| < θ. We may and do choose$λ_{0}$closed enough that the comparisons and local-character bounds used here fit below it.

Inside B choose lists$x_{i}, i <$θ, so that every$D^{K} (x_{i},$Z) equals$D^{K}$(x, Z) and all the$x_{i}$together are independent over$M_{0}.$To make the successor choice, include in the bounded match the entire enumeration of$M_{0},$Z, and all earlier copies. The original x, being independent over P (B), is independent from those earlier copies. Saturation realizes its joint diagram inside B. Diagram equality is witnessed by an isomorphism, so it preserves every finite independence comparison over$M_{0}.$The total parameters at every choice are bounded at the level of B.

Take a strong section$N ≤_{K} B$of size$λ_{0}$containing$M_{0},$Z, and all the copies. Their finite sublists have product type over$M_{0}.$The independent-list and finite-domination conclusions of Theorem 7.13 give a continuous witness chain$(A_{i}: i ≤$θ) inside N, starting at$M_{0},$in which$x_{i}$is free over$A_{i}$from$M_{0}$and is included in$A_{i+1}.$One may keep the chain inside N: at each step primeness embeds the required all-dominated increment into N over its already placed base and the specified next list. At limits finite domination keeps the next finite list free, and unions remain strong in N.

Since cf(θ) > |Z|, local character applies to$tp(Z/A_{θ}).$It is free from some$A_{i}.$For a later j < θ, its restriction to$A_{j+1}$is free over$A_{j},$so Z and$x_{j}$have product over$A_{j}.$The type of$x_{j}$over$A_{j}$is free from$M_{0}.$The base-change identity in Proposition 6.12 therefore says that$x_{j}$has product with Z over$M_{0}.$In particular$D^{K} (x_{j},$Z) is determined by$p_{0}$and$tp(Z/M_{0}).$

A known product of the$p^{B}$has this same joint diagram with Z: products of free lifts are free lifts of products, and one may restrict the resulting type to$M_{0}$together with Z. Since$D^{K}$(x, Z)$= D^{K} (x_{j},$Z), the two candidate types over B agree on every test of the uniform comparison size. Bounded testing makes their full types equal. This proves the converse.

## 10.3 Eliminating proper extensions with unchanged geometry

The obstruction considered here is related to Vaughtian pairs: proper extensions of the same cardinality with no new realizations of a fixed nonalgebraic type; compare [GV06], where the type is based on a limit model. Here finite marked systems and exact boundary lifting eliminate the obstruction in the pointed setting.

The next use of the marked construction requires a type prescription that can be chosen from a fixed set before choosing the common level. We record the uniformity explicitly.

Lemma 10.8 (Anchoring a singleton type). There is a fixed cardinal β, depending on the single-model template, its singleton comparison bound, and the fixed point, with the following property. If A is a sufficiently closed pointed model and r is a nonalgebraic singleton type over A, a list c ⊆ A of length at most β can be named so that:

1. the joint stabilized diagram of c,$m̄_{0},$together with a fixed majority prescription, defines a unique nonalgebraic singleton type$r^{B}$over every sufficiently closed model B having that named diagram;

2. the prescription at A is r, and the family$r^{B}$lifts freely along arrows preserving the names, including across eligible levels;

3. the prescription occurs at arbitrarily large eligible single-model levels.

The possible descriptors obtained this way form a set, with their length bound independent of ∥A∥.

Proof. Fix a sufficiently large uniform testing arity τ for singleton types, including the bound needed to apply compact placement to those tests. The approximation construction for Theorem 6.10 gives a list$c = (c_{i}: i <$β') of approximations in A that computes r by majority on all these tests. Its length and all ancillary approximation data can be bounded by one cardinal β, independently of the level. Choose the length larger than the exception bound for the tests; increase β also to include the fixed point data. The prescription is the value attained by all but the permitted number of entries in$D^{K} (c_{i},$z), for each test z of arity at most τ.

Freely lift the actual r to arbitrarily large eligible models containing A. Query matching over the fixed approximation list shows that these lifts compute exactly the same majority prescription.

They are nonalgebraic by Lemma 10.1. For another sufficiently closed pointed B with the same named diagram, embed B into such a larger instance, respecting the names. This is possible by bounded-diagram homogeneity and mixed placement. Restrict the lifted type to that copy of B. It is nonalgebraic, since its realization is outside the larger parameter model, and query matching makes its bounded answers the prescribed ones.

Any two types having these answers are equal by the singleton comparison bound. Thus the construction is independent of the larger instance and the chosen embedding. A free lift along an arrow preserving the names has the same prescribed answers: the approximation evaluation is transported by matching each query over the named list inside the old base. Uniqueness therefore identifies it with the prescribed receiving type. At A the answers are those of r by the choice of c.

The list lengths have a fixed set bound. Their stabilized diagrams, the fixed testing arity, and the majority rule range over a set of descriptors. Only descriptors realized at arbitrarily high eligible single-model levels are needed; the preceding construction proves that the descriptor extracted from an actual r has this property. The named diagram itself can be witnessed at one fixed eligible level large enough for arity β, by saturation for diagrams from larger levels. Proposition 5.7 therefore applies with a lower threshold depending on β and the original working scheme, rather than on ∥A∥. In particular, extracting the names from a model of size λ does not require moving above λ in order to use the pointed working scheme at that level.

Theorem 10.9 (No proper pair with unchanged points at one level). There is a sufficiently large cardinal$λ > λ_{0}$such that there is no proper strong inclusion$A <_{K} B$of pointed models of size λ with P (A) = P (B).

Proof. Take the set of anchored descriptors from Lemma 10.8. Choose λ at a common level for all finite marked constructions for these descriptors, using Theorem 13.5. Require also all the relevant single-model and pointed bounds, and$λ > λ_{0} +$β. This is a choice uniform in the possible descriptor. In particular the choice does not depend on a pair that might later be assumed to exist.

Suppose toward a contradiction that$A <_{K} B$is such a pair, and choose a ∈ B \ A. Apply Lemma 10.8 to r = tp(a/A) and name its list c. We work in the pointed scheme also naming this list, with its fixed joint diagram. Write$C_{n}$for its n-fold marked iteration with the root prescription r, as in Theorem 9.3.

Every one-step all-dominated increment of this scheme has no new P-points. Indeed, pointed categoricity carries its base, including the named list c, onto A. Transporting the witness$A <_{K} B$back gives an extension with a realization of the required r and unchanged P. Primeness embeds the all-dominated increment into that extension over its base and mark. Since strong maps preserve and reflect P and fix the base, the increment has exactly the base points.

It follows by induction that the P-points in the top of every$C_{n}$object are precisely those in its root. For the induction step, its lower and upper layers are$C_{n−1}$objects and hence each has the points of its own root. Projection onto the new axis is a valid one-step marked increment by Theorem 9.3. The two roots therefore have the same points, proving the assertion for the entire object.

We next construct coherent finite systems. For each n < ω choose an object$J_{n} ∈ C_{n}.$For every s ⊆ {1,..., n} choose an isomorphism

$e_{n,s}: J_{|s|} −→ P_{s} J_{n}$

such that these maps commute with all further face projections, using the increasing identifications of finite index sets. Here the full face map is the identity. To make these choices, induct first on n and then on the size of a proper subset s. For a proper subset u of the axes of$J_{|s|},$let t be the corresponding subset of s. The boundary map for$e_{n,s}$on this face is$e_{n,t} e_{|s|,u^{−1}},$with the indicated index identifications. The already chosen maps make these boundary prescriptions compatible. Theorem 9.8 extends them to the desired isomorphism. At dimension zero it is simply pointed categoricity. This constructs every$e_{n,s}$with the asserted commutation.

For the finite subsets s of any ordinal I, take a tagged copy of the top vertex of$J_{|s|}.$If s ⊆ t, use the top component of$e_{|t|,u}$followed by the inclusion of that face into the top, where u records the positions of s in the increasing list of t. The preceding commutation gives a directed system of strong maps. All its roots are copies of the same actual$J_{0},$and no vertex has more P-points than that root.

The marks corresponding to different indices of I are distinct in this directed system. It suffices to inspect a two-axis object. Its new mark lies in the root of its upper one-axis layer, whereas the old mark is the nonalgebraic mark of that layer and is outside its root. Face isomorphisms preserve the marks, so the distinction persists under all transition maps.

Take I of cardinality µ > λ, where µ is a sufficiently closed single-model pointed level. The ordinary directed colimit in the AEC exists: a coherent diagram of injective maps is realized as a diagram of inclusions in its direct limit, and the directed-union axioms apply. There are µ finite subsets of I, each contributing at most λ elements, and there are µ distinct marks. Thus the colimit N has size exactly µ. Every element of N comes from one finite vertex. Preservation and reflection of P give P (N)$= P (J_{0}),$|P (N)| ≤ λ.

The enumeration of its distinguished$M_{0}$retains the fixed stabilized diagram ∆ under the strong colimit embeddings.

On the other hand, there is a pointed model of size µ with more than λ points. Start with any pointed model of that size. Successively realize a nonalgebraic free extension of$p_{0}$outside the current model, for$λ^{+}$steps. The receiving models and their unions may all be kept of size µ. The new realizations are distinct and belong to P, so the union has at least$λ^{+}$points. Pointed categoricity at µ would make this model isomorphic to N over$M_{0}, a$contradiction.

Only the stationary prescription r was lifted to higher levels. The assumed witness with unchanged P was used solely at λ. The large colimit used the full AEC directed-union axioms, rather than a same-level closure assertion for a marked scheme.

Corollary 10.10 (No-growth and rank on the entire tail). Increase the threshold λ if necessary to include the bounds for the fixed point diagram. In arbitrary cardinalities, if$A ≤_{K} B$are pointed models with ∥A∥ ≥ λ and P (A) = P (B), then A = B. Moreover, for every pointed model M with ∥M ∥ > λ, |P (M)| = rk(P (M)) = ∥M ∥.

The point sets of strong submodels are relatively closed, and relative bases and finite basis supports are available as in Theorem 10.5; no eligibility condition is imposed on these arbitrary cardinalities.

Proof. Suppose that a ∈ B \A and P (A) = P (B). Construct increasing strong submodels$A_{i} ≤_{K} A$and$B_{i} ≤_{K} B$of size λ, for i < ω, all containing the distinguished copy of$M_{0},$so that

$A_{i} ≤_{K} B_{i}, a ∈ B_{i}, P (B_{i}) ⊆ A_{i+1}.$

For the successor choice,$P (B_{i})$has size at most λ and is contained in A, so the Löwenheim–Skolem axiom places it, together with$A_{i},$in the next$A_{i+1}.$Choose$B_{i+1}$to contain$A_{i+1} ∪ B_{i} ∪${a}.

Coherence makes all the required inclusions strong. The two unions$A_{ω} ≤_{K} B_{ω}$have size λ. The point diagram restricts correctly to them, and

⋃

$P (B_{ω}) =$i<ω$P (B_{i}) ⊆ A_{ω}.$

Thus their point sets are equal, while$a ∈ B_{ω}$\$A_{ω}.$This contradicts Theorem 10.9.

Now let ∥M ∥ = κ > λ. If |P (M)| < κ, choose a strong submodel containing$M_{0} ∪ P$(M) of size at most |P (M)|$+ λ_{0}.$Enlarge it inside M, if necessary, to a strong submodel of size at least λ and still less than κ. It has the same P as M, contrary to the assertion just proved. Hence |P (M)| = κ. If H is a basis of P (M), the closure bound gives

κ = |P (M)|$= | cl_{M}$(H)| ≤ |H|$+ λ_{0}.$

Since$κ > λ ≥ λ_{0},$it follows that |H| = κ. The final assertions were established in Theorem 10.5 independently of eligibility.
