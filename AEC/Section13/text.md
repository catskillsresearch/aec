# 13 Uniform definitions and common closure levels


The arguments above use two different finite inductions. The first iterates marked increments, with a fixed prescription in the root sort. The second ranges over finite geometric shapes. In each application we need one cardinal at which every finite stage is available. We now give the definability and closure bookkeeping that permits this in ZFC. The fixed point data, and subsequently the threshold furnished by the marked-increment application, are fixed before performing the bookkeeping for the geometric application. Thus the two applications may use different closure functions.

The bookkeeping has three stages. First we express the finite systems and their required properties by fixed formulas at a given cardinal. Next we list the bound requests and the order in which each construction uses them. Only after those formulas are fixed do we choose a common majorant and construct the nested eligible subclasses introduced in the preview in Section 5. Their absorption property will allow each finite induction to retain an unbounded supply of levels.

## 13.1 Set definitions at a given cardinal

Proposition 13.1 (Uniform finite-depth definitions). Fix the set code for K from Proposition 2.3, its order template, and the fixed data used in either of the two applications. There are a set D of normalized finite descriptors and fixed first-order formulas of set theory with the following properties.

1. Given d ∈ D and an infinite cardinal µ, the formulas define sets of standardized objects and arrows. For marked descriptors these sets are obtained by a finite recursion whose length is an input; at eligible levels they give precisely the categories$C_{n}.$For a geometric descriptor they give the systems$G_{L}$and their arrows.

2. The formulas define orbit comparison, comparison of realized types over a base, relative isolation, the prescribed root marginal, and the finite projection and boundary conditions.

On levels with the requisite working package these definitions agree with their mathematical meanings in the preceding sections.

3. There is one unary adequacy formula, with a descriptor as parameter, which can assert any of the packages needed during the finite inductions: the individual working conditions, the chart clause using$D_{F},$the projection and type conditions, amalgamated completion, exact boundary lifting, or the geometric categoricity and basis conditions. Its use does not require a formula for a previously chosen closure function.

4. All candidate term templates, named patterns, and finite descriptors needed in the two inductions can be chosen from D. In particular, their codes have one set-sized bound independent of the finite depth and of the level cardinal.

These are definitions at every cardinal; a definition by itself makes no claim that the cardinal is eligible.

Proof. We specify the set recursion and the formulas used in it. The small-model code for K defines membership and strong substructure by the directed union formulas in Proposition 2.3. These are fixed formulas with a set parameter. They are therefore available in all the following set constructions.

Standardized structures and tuples. For a fixed finite descriptor and cardinal µ, use a separate copy of µ for each vertex sort, and represent each inclusion by its map. Pointed data and marks are represented by constants in their indicated sorts. This convention allows a proper same-cardinality inclusion: it is an injective map between the two copies, rather than the identity map on a common universe. A finite diagram of such structures is specified by sets of finitary relations, function graphs, constant values, and maps between these carriers. The collection of all candidates is a set. An arbitrary diagram of the specified cardinalities has a copy in this collection, by choosing bijections in its finitely many vertex sorts.

The bounded tuples used below are functions with ordinal domain of cardinality less than µ, together with a vertex occurrence for every coordinate. It suffices to use domains that are cardinals below µ: other enumerations are obtained by reindexing. All such functions form a set. A fragment in a system is likewise an occurrence-tagged subset of its finitely many carriers. Equalities between occurrences are tested after their specified maps into a common vertex; they are not inferred from equality of sort tags.

Raw comparison relations. Suppose sets O and A of objects and arrows have already been constructed. Isomorphism is expressed by an arrow with a two-sided inverse in A. Put

$Orb_{O,A}$(Y, u; Z, v) ⇐⇒ ∃h: Y ≃ Z (h(u) = v).

Here, and in the formulas that follow, the quantified objects and arrows belong to the displayed sets. If e: X → Y and f: X → Z are arrows, put

$Eq_{O,A}$(X; e, Y, u; f, Z, v)

⇐⇒ ∃W ∃g: Y → W ∃h: Z → W ge = hf and g(u) = h(v).

These are formulas about sets. At a level where amalgamation has been proved, the second relation is precisely equality of the realized types used in the one-dimensional calculus, as characterized in Theorem 6.6. Until amalgamation has been established we use the displayed relation itself, without taking a quotient or claiming transitivity.

Here is the isolation test in full. For e: X → Y and bounded b, c in Y, the test is

∃z$∈ X^{<µ}$∀(f: X → Z) ∀b', c' Eq(X; e, Y, b; f, Z, b') ∧ Orb(Y, (b, c, ez); Z, (b', c', f z))

=⇒ Eq(X; e, Y, (b, c); f, Z, (b', c')).

The tuples b', c' have the same lengths and occurrences as b, c. The universal quantifiers range over all extensions in O, not just over the objects about to be defined. The displayed notation$X^{<µ}$includes the occurrence tags. By the diagram and amalgamation clauses of the working package, this is exactly isolation relative to b: z enumerates an isolating fragment. Requiring this formula for every bounded c in Y defines all-domination over X + b. In particular, this test uses only O and A of the preceding category.

Root prescriptions and free lifting. The base descriptor includes the fixed named pattern. A prescription for a root type is given by the approximation code already used in Lemma 10.8: a named bounded list of approximating tuples, its joint underlying K-diagram with the point, and a test arity sufficient to determine the type. For any test at that arity, the requested comparison is the comparison given by all but the allowed number of exceptions in the list. The allowed number is |z|$+ ℵ_{0}$for a parameter test z, and the list is longer than this number. Checking this rule for every such z is a fixed formula using the underlying K-diagram predicate. Existence and uniqueness of a type satisfying it, and its free lifting, are the conclusions proved when the prescription is introduced; they are not part of the assertion that the formula is defined.

This root test is applied after forgetting to the root K-sort. The projection type correspondence in Proposition 9.1 identifies it, at the levels under consideration, with the required type over the whole system. Thus the definition does not successively quote a new formula for a type at each marked depth.

For completeness, references to free lifting in an adequacy condition also have a fixed set interpretation. Let p be represented by (A → Y, u), and let q be represented by (B → Z, v) over an extension j: A → B, with q restricting to p. This is a same-level test: A, B, Y, Z are objects at µ. Mixed lifting is derived below using approximation costs bounded at the source level. For an infinite σ ≥ |u|, an approximation test on$I = (u_{i})_{i<θ}$requires the following. For each parameter tuple z of length at most σ in the base, and each corresponding subtuple of u and the$u_{i},$at most

|z|$+ ℵ_{0}$indices have a joint diagram with z different from that of the realized type. The free-lift test is ∀σ (|u|$+ ℵ_{0} ≤ σ <$µ) ∃θ (σ < θ < µ) ∃I$∈ (A^{|u|})^{θ}$

such that I passes this test for p over A and jI passes it for q over B. Here σ, θ are cardinals, and all joint diagrams are computed in the indicated realizing objects. The approximation construction gives these sequences for a free lift. Conversely, compare a sequence witnessing this test with the sequence computing the free lift at the same arity. Move a parameter query from B into A over both sequences by bounded saturation. Each majority then computes the original type on the moved query; the two majorities agree because their sequences have lengths exceeding their exception bounds. This proves equality with the free lift on every bounded test, and hence equality of types by Theorem 6.6. All the sequences, tuples, exception sets, and realized types in this test range over sets at the given cardinal. This supplies a formula without a satisfaction predicate for a category definition.

The marked recursion. Let$O_{0}$(µ) be the standardized pointed K-models with the specified named pattern, and let$A_{0}$(µ) be their strong maps preserving the names. Given$O_{i}$(µ),$A_{i}$(µ), form their raw comparison and isolation relations as above, and set

$O_{i+1}$(µ) = {(e: X → Y, b): X,$Y ∈ O_{i}$(µ),$e ∈ A_{i}$(µ),

b passes the prescribed root test,

∀c$∈ Y^{<µ}$(b, c)/X passes the relative isolation test}.

An arrow from (e: X → Y, b) to (e': X' → Y', b') is a pair (f: X → X', g: Y → Y') of arrows in$A_{i}$(µ) with ge = e' f and g(b) = b'. This defines$A_{i+1}$(µ) by Separation. Reading a pair as two layers gives the next axis; the earlier axes, their maps, their marks, and the root projection are part of its finite diagram code.

The operator in these two definitions is fixed. A finite sequence

$(O_{i}$(µ),$A_{i} (µ))_{i≤n}$

satisfying the initial condition and this operator is a set and is unique. Existence follows by finite recursion using Power Set and Separation at each step. Consequently the assertion that a candidate belongs to its last object or arrow set is one first-order formula with n as an input. It is not a sequence of truth definitions on the universe. Induction, using the prescribed-type correspondence and Theorem 8.6, identifies this recursion with the intended$C_{n}$at eligible levels. Raw tests at other levels have no role in that identification.

Geometric descriptors. Such a descriptor contains a finite axis set and its active-label family. The shape condition is a finite calculation. Membership in P, and independence of a finite list in P, are tested in a strong$λ_{0}-section$over$M_{0},$as in Theorem 10.5. A section, an isomorphism of sections, and a finite product witness are set-coded data. The independence predicate so obtained is fixed, with$M_{0}, p_{0}, λ_{0}$as parameters. For a set H in a vertex, independence means that every finite subset is independent; spanning means that every relevant point is in the closure of some finite subset of H. Thus the existence of pieces$(H_{s})_{s∈L}$forming the required partitioned basis is a first-order condition on subsets of the finitely many carriers. Their required cardinalities are expressed by bijections.

The arrow condition is componentwise strongness together with preservation of finite independence in a vertex modulo its proper lower vertices. A dependence modulo the lower vertices has a finite witness there. This gives a fixed formula, equivalent to extendibility of basis pieces by Definition 11.1. The bases are existential witnesses in these tests; they are not extra structure that an isomorphism must preserve. Inactive vertices and the equalities forced by their largest active lower label are included as part of the system condition. This constructs the geometric object and arrow sets without a recursion in formula complexity.

A set of template codes. Choose an infinite cardinal$b_{0}$bounding the fixed vocabulary, template labels, point code, and the lengths and pattern codes allowed for the named root prescriptions. The latter have such a bound because the approximation list length is bounded in terms of the underlying K-testing arity, independently of the level where an actual pair is found. Order and equality patterns for lists of this fixed bounded length form a set.

At one marked-template extraction, the expansion consists of old chart labels and representation tags, finitely indexed coordinate functions, the finite system maps and mark information, a retraction-index sort with its evaluation map, and the vertex LS-witness functions. For a vocabulary and label bound b, these symbols have a cardinal bound depending only on b and the fixed data. There is no symbol for every element of a sample or every entry of a sample-sized diagram table: sample entries and retraction indices are elements of sorts. Complete atomic diagrams on finite lists of terms are subsets of the set of atomic term instances and their negations.

For definiteness, increase bounds generously and take

+

$b_{m+1} = 2^{2^{bm}}, b_{∗} =$m<ωsup$b_{m}.$

Induction bounds the languages, finite-term sets, and their possible diagram codes at each finite extraction by a corresponding$b_{m}.$Normalize symbol names by ordinals below these bounds. The union over m < ω of the resulting sets of candidate codes is a set containing every candidate template needed at finite depth. The explicit geometric tile templates obey the same bound. Finally take finite diagrams of these codes, together with finite axis data, root codes, and the flags described next. This is the promised set D.

One adequacy formula. Use the following fixed menu of assertions. A descriptor can request any finite selection of them for any of its indicated lower schemes. Every selection, including a preliminary geometric categoricity or basis selection, requires a strong limit cardinal of countable cofinality above all its fixed parameter bounds.

1. For every well-order I of cardinality µ, the indicated term interpretation F (I) is an object, every object at the level is isomorphic to F (I), and substitution along every same-level order embedding gives an arrow. The term interpretation is its set of terms modulo the template equality relation. It suffices to quantify over orders on a fixed copy of µ, so this is a first-order test on sets. In particular, validity of only the presentation on the initial ordinal µ is not the presentation clause used here.

2. Same-level arrows preserve bounded tuple orbits, and comparison of bounded tuples in well-ordered charts is exactly the fixed comparison$D_{F}$of Proposition 5.9.

3. A chain of objects whose union has the level cardinality has an object as its union. For this test it suffices to use a chain with at most µ indices: from any chain with a union of size µ, choose stages covering its elements in all vertex sorts. The resulting subchain has the same union and has order type below$µ^{+}.$

4. The root prescription, the indicated projections on objects and arrows, diagram comparison on projection sorts, and the stated type correspondence over a base hold. The comparisons use the raw relations above, now together with the requested working conditions. The free-lift clause uses the approximation test just specified.

5. A compatible boundary arrow has an amalgamated completion, or a compatible boundary isomorphism extends to an isomorphism of the whole objects, as indicated by the flag. These assertions quantify over the finite families of maps on the proper axis subsets and the object and arrow sets at this cardinal.

6. For a geometric descriptor, the indicated categoricity, lifting with prescribed nonroot basis bijections and root map, or lifting over a fixed base with prescribed complementary basis bijections holds. The pieces and the bijections range over sets of subsets and functions of the standardized carriers.

7. A designated term interpretation T into an indicated lower scheme has the following properties.

Its values on the orders used by the specified natural layout are objects of that lower scheme, its same-level order substitutions give lower-scheme arrows, and comparison of its bounded term lists agrees with the lower scheme’s$D_{F}.$Require explicitly that this comparison is natural in the new interpretation: two instances with the same T-labels and joint horizontal support pattern have the same lower-scheme diagram, and the descriptor’s support substitutions preserve the designated term parts. This is the comparison used for the natural-layout test; arbitrary old-chart representations without this horizontal naturality assertion do not suffice.

Orders, their finitely many designated parts, term evaluations, and support patterns are set-coded at the level. This flag may be requested for the base and upper interpretations of a new marked pair template while omitting the new pair’s chain and chart flags. It uses the already established lower-scheme comparison.

There are only finitely many forms in this menu. The geometric categoricity and basis item can be used before the diagram clause has been obtained for the current geometric shape. A descriptor records which assertions are currently required, and for which finitely many lower descriptors. Bounded quantification over that finite record yields one formula, denoted Adeq(d, µ). Its ingredients were all defined by set operations or by the fixed underlying K and$D_{F}$formulas. This proves all four assertions.

The definitions above describe objects and assertions at one cardinal; they do not themselves establish eligibility there. Before collecting the bounds, we check how the individual adequacy conditions supply the maps and comparisons between different eligible levels that the earlier constructions use.

Lemma 13.2 (The mixed-level interface). For either application, suppose the relevant individual adequacy conditions of Proposition 13.1 hold on a class S of levels, above the fixed parameter bounds. When the full individual working conditions, including the chart clause, are requested, the mixed presentation, coherence, LS, diagram, saturation, and map conditions needed in the preceding arguments hold on S. A preliminary descriptor requests only the corresponding already established clauses: in particular, its natural-interpretation flag supplies comparisons in the indicated lower working scheme and makes no assertion of a new pair’s chain closure or chart clause.

Proof. Presentation arrows across levels are supplied by the construction of the templates: the vertex term-hull LS witnesses give componentwise strongness in the marked application, and the tile specialization of Proposition 11.6 gives the additional basis condition in the geometric application. Coherence is componentwise coherence, with the finite independence test for geometric arrows. Once a componentwise union is an object, its arrows and its common-upper-bound property, including into a larger object, follow from the AEC chain axioms and, for geometry, finite character of independence.

Suppose an object X at ν ∈ S maps to an object Y at a larger µ ∈ S. Present Y on a well-order. The image of X uses at most ν positions: each of its ν entries has finite term support, and there are finitely many vertices. Include these positions in a well-ordered subpresentation of cardinality ν, also including the fixed named positions. Coherence gives an arrow from X to this subpresentation. This is mixed LS.

For a tuple bounded at ν, the latter arrow preserves its orbit by the same-level adequacy condition. The chart clause identifies that orbit with$D_{F}.$Inclusion of the subpresentation in the large chart leaves the labeled support pattern unchanged, so the same$D_{F}$test computes the diagram in Y. This proves preservation along arbitrary mixed arrows. A bounded well-ordered pattern from a larger chart can also be placed in an order of size ν. When its old tuple has the same diagram as a specified tuple in a ν-object, the same-level chart clause gives an isomorphism matching those tuples. Transporting the enlargement through that isomorphism proves the required mixed-level bounded saturation.

Root prescriptions pass along mixed arrows because the approximation lists give the same majority comparisons there. To compare the full system types after projection, apply the type correspondence at the receiving level to those equal root marginals. Finally, the criterion for maps obtained by exhausting bounded tuples is componentwise the strong-submodel criterion of the working package. In the geometric case its additional condition is a finite independence comparison, preserved by the matched system diagrams. These arguments verify the mixed clauses without inserting them as new proper-class parameters in the unary adequacy formula.

## 13.2 A fixed register of bound requests

We specify what is included when a closure requirement is invoked. Given a uniform unary formula S(µ) and a bound request with ordinal input α and descriptor d, write

(

$B_{q}$(d, α; S) = the0, least ordinal satisfying the request, ifotherwise.such an ordinal exists,

In this notation q belongs to the finite register below. The notation does not permit an arbitrary formula as a value of q, or an arbitrary class as a parameter S.

Lemma 13.3 (Uniform bound register). All the refinements in one application of the one-dimensional tools, one marked-increment step with its projection and boundary arguments, or one geometric categoricity, basis, or boundary step are expressible using a fixed finite register of first-order bound requests. Their parameters are finite descriptors, ordinal size inputs, and unary adequacy tests from Proposition 13.1. Any references within one such step to earlier refinements can be eliminated by a fixed finite number of substitutions, independently of the input depth. Every bound request needed on the levels where its preceding hypotheses have been established has an ordinal witness.

Proof. Here is the register; its descriptions specify first-order tests, rather than codes for formulas of increasing depth.

Cardinal, order-pattern, and partition bounds. Include successors, power sets, and their bounded iterations. For example, profile growth through$α^{+}$stages is bounded by the recursion$a_{0} ≥$α,$a_{ξ+1} = (2^{a_{ξ}})^{+},$with suprema at limits, for$ξ ≤ α^{+}.$This is a set recursion with ordinal parameters. Cut filling and saturation of order patterns of size at most α use the same operations and the corresponding$α^{+}$-stage construction. The finite-arity partition request is the least ordinal on which every coloring of k-element subsets by the given color set has a homogeneous subset of the prescribed size; k and the size bounds are descriptor or ordinal inputs. The partition argument used to construct the order templates proves existence. Small trees and their parameter accumulators use successors, powers, and the least ϵ with$2^{ϵ} >$χ. These operations cover the chain lengths and cardinal costs in the domination and return-tree arguments.

Placed comparison and syntax tests. For a specified permitted layout and tuple arity, the comparison request asks for a bound on the size of a parameter test witnessing inequality between two placed comparisons. More explicitly, quantify over an eligible level, its indicated order layout, the two candidate term lists in order enlargements, and the parameters generated by the designated parts. If their comparisons differ on some bounded parameter list, require that they differ on one of size at most the proposed bound. Inequality is evaluated in a larger eligible padded presentation, using isomorphism to a well-ordered chart, or equivalently by its$D_{F}$comparison where the chart clause has been obtained. All the objects and positions involved in a particular test are sets. Universal quantification over the level cardinal is an ordinary first-order quantifier.

The permitted layouts are the whole-model layout, designated vertex parts, and finitely segmented or tiled layouts with the prescribed order and colors. Their codes belong to the descriptor set. The ordinary and rationally tiled ordinal-vector arguments of Proposition 6.3 and Lemma 12.5 prove that this request has a uniform witness. The syntax request asks for a test size at which the fixed$D_{F}$comparison on patterns of a specified size is already determined. The set of such patterns and the set-structure back-and-forth construction in Proposition 5.9 prove existence. Neither request mentions a truth predicate for$C_{n}.$

P

requestFor theincludesrationallythe boundedtiled layoutsfrozen datai$(H_{i}$of× LemmaQ) used12.5.in theThatgeometriclemmaapplication,supplies its thewitnesscomparisonalso for

candidates in arbitrary enlargements of the underlying E-order. The exceptional fibers, their frozen positions, and the set of cut coordinates have bounds in the input arities and fixed descriptor; no new dependence on the level or the finite depth is introduced.

Approximation, compactification, and isolation bounds. The approximation and compactification constructions take a comparison bound and a profile bound at the specified arity, increase the lengths to dominate the exception counts, and perform the bounded power-set iteration just described. Thus their sizes are fixed compositions of the first two requests and cardinal operations. The isolating-fragment bound is the size of the initial supports, the bounded initial parts of the candidate blocks, and the terms on those supports in the proof of Proposition 7.3. These again use the same comparison and cardinal requests. The construction of all-dominated objects uses larger input ordinals in these requests, mixed LS, and the indicated successor-length recursions; it introduces no new form of predicate depending on the marked depth. The existence assertions used here are Proposition 7.8 and Theorems 7.9 and 7.13, with the mixed interface just verified.

Eventual orbit thresholds. The remaining request asks for the first threshold above which a specified reversal, orbit-preservation, or stabilization assertion holds at the eligible levels and the indicated arity. The assertion itself uses the standardized object sets, arrows, and orbit relation defined above. Thus the threshold test has the form

∀µ S(µ) ∧ µ > β =⇒ R(d, α, µ),

or its two-level version, with R one of these fixed orbit assertions. The reversal and stabilization arguments prove the existence of the threshold when the current categoricity and the previous required conditions hold on the unbounded eligible class. The use for geometric shapes has exactly those hypotheses by Proposition 11.7. Passing from these thresholds to diagram homogeneity also requires smaller eligible levels cofinal below the final level; that requirement is recorded separately as a limit-point refinement.

We check that this list accounts for a whole generic step. In a marked step, extraction uses partition bounds, the underlying comparison and isolation bounds, and arbitrarily large samples. It chooses a template from the set established in Proposition 13.1; see Lemma 8.3. After that choice, the two-part comparison of Lemma 8.4, used in Lemma 8.5, is the placed comparison request with this template as parameter. The downward isolation argument requires the same bounds and sufficiently closed smaller levels. Orbit comparison and saturation use the transport argument; the passage to the unary chart clause uses the syntax request. Projection, completion, and exact boundary lifting then use the ordinary comparison requests, the prior unary conditions, and the tree costs; exact lifting may require one further supply of cofinal smaller levels. These are respectively the constructions of Proposition 9.1 and Theorems 9.6 and 9.8.

For geometry, first use the current categoricity condition and prior basis conditions as unary inputs to the eventual orbit request, then require smaller eligible levels and the chart syntax bounds. Basis lifting and exact boundary lifting use the same one-dimensional and tiled-layout requests and tree costs, by Theorems 11.9 and 12.2. A simultaneous projection calculation or a maximum over finitely many lower descriptors is expressed by bounded quantification over that finite descriptor. It does not require successively inserting their formulas into one another.

Within each of these generic proofs there are finitely many successive uses of closure and of cofinal smaller levels. Label those positions in the proof in their order. The predicate for a position is the initial adequacy predicate conjoined with the earlier stated threshold, closure, and limit-point conditions. Substituting these descriptions at the finitely many positions gives a fixed formula for each request. The number of positions is attached to the generic proof, not to the finite axis count; finite lower-scheme lists are handled by the bounded quantification just described. This produces the asserted finite register with S eliminated in favor of its uniform defining formula.

The eligible predicates in a marked step. The following substitution order also previews the common-level induction at the end of this section. References here to retaining$G_{j}$use the advance notation in Section 5; the actual classes and their absorption property are constructed below, after the register is fixed. They supply levels for that induction, not parameters for the requests being defined here.

Let$S_{0}$be the unary conjunction of the full individual working conditions for the input scheme and the projection and stationary-prescription conditions already established for the finitely many lower descriptors. The mixed interface supplies their mixed working conditions. First refine$S_{0}$by the testing, approximation, isolation, and domination bounds of Sections 6 and 7; call this class$S_{1}.$On its sufficiently closed members the actual constructions give the samples used in Lemma 8.3. The induction maintains that$S_{1}$is unbounded by retaining$a G_{j};$unboundedness of an arbitrary class alone would not justify this step.

After selecting$F^{b},$let R(µ) be the conjunction of$S_{1}$(µ), the individual presentation flag for$F^{b},$and the natural-interpretation flags for its base and upper values in the old scheme. Evaluate the testing request for the layout$U_{H} ∪ A_{H'}$on this preliminary class R, using the old scheme’s$D_{F}.$Lemma 8.3 supplies the individual validity and natural interpretations; Lemma 8.4 reduces the comparison to the old working scheme, where the ordinal-vector argument of Proposition 6.3 supplies its uniform bound.

Now refine R by that testing bound and its placement and arity costs; call the resulting class$S_{2}.$Thus$S_{2}$is the output of this refinement, not the eligible predicate in its own defining request. The preliminary predicate R uses only the earlier costs and the two specified kinds of flags. Neither the request nor its witness uses$a D_{F^{b}}$chart clause or chain closure for the pair scheme.

At members of$S_{2} ∩ Lim(S_{2})$closed under the same arity costs, Lemma 8.5 proves pair-chain closure, including bounded tuples spanning the chain. The actual pre-closure orbit argument and this chain assertion then give Theorem 8.6; only now impose the syntax bound for$D_{F^{b}}$and request its chart clause. Projection correspondence and amalgamated boundary completion follow after the fixed comparison and tree-cost refinements in Section 9. The fixed-parameter boundary argument and exact lifting may add one further limit-point refinement to obtain smaller levels where completion already holds. Each displayed eligible predicate is thus a finite conjunction of unary flags, previously listed bound closures, and limit-point conditions. Substitution follows this displayed order; no predicate for a previously chosen$G_{j}$or closure function is inserted into a bound request. More generally the auxiliary subclass T in the eligible-level convention is used only to ensure an unbounded supply of levels through these finite refinements. It is not an additional parameter of any request. In the present induction$T = G_{j}$supplies this existence assertion, while each request still uses the unary adequacy predicate and the finitely expanded refinements just displayed.

The eligible predicates in a geometric step. The first assertion of Theorem 11.9 for the current shape follows from the previously proved assertions for its finitely many lower shapes. Start with the unary conjunction of this current categoricity assertion and the needed lower-shape assertions. The structural and tiled-presentation proofs give the actual arrows, coherence, union conditions, and mixed containment used by Proposition 11.7. Its finite-tile alignment and orbit calculation prove eventual reversal on this class. The first route in Proposition 5.8 then proves stabilization; impose those arity bounds and a limit-point refinement within the current eligible class. Actual diagram homogeneity is proved at the retained members before the$D_{F}$syntax bound is imposed.

The four subsequent claims in the proof of Theorem 11.9 use this established package, the preceding one-dimensional bounds, and finite tree costs. They prove the relative-basis assertion at the retained levels. For exact boundary lifting, include the already proved exact assertions for all proper restricted shapes in the initial unary conjunction. The tree and unoccupied-strip proofs of Theorem 12.2 add only the indicated layout, support-closure, and tree-cost refinements. Increasing the number of axes changes the finite list of lower descriptors and the ordinal size inputs; it does not add a new kind of eligible predicate or a new position in this generic substitution order.

Finally, the witness assertions are precisely the uniform bounds proved in the cited constructions with their stated hypotheses. An irrelevant descriptor, or a stage whose hypotheses fail, may give a request with no witness. Its value 0 makes a total definable ordinal function and has no mathematical force. At a used stage we invoke the preceding construction to establish existence before applying the bound. In particular, totalization supplies neither an adequate template nor a missing lifting or testing witness.

## 13.3 The common majorant and its limit refinements

We now construct the hierarchy used in the preceding previews. The register and its finite substitutions have been fixed independently of this construction; the common majorant bounds their values, while the limit refinements supply smaller eligible levels cofinally below a new level.

Choose a cardinal ϑ above the hereditary sizes of the normalized descriptor set and all fixed parameters. This is one cutoff, chosen before any finite-depth induction; it includes all candidate templates, not just those already selected. For α ∈ Ord, take the supremum of the values of all the functions in the expanded finite register, for every descriptor and for all ordinal inputs at most α. Finite lists of size inputs are included by taking all their coordinates at most α. Each such collection is a set, and each request has been totalized, so Replacement bounds its values. We may therefore choose a fixed, monotone definable ordinal function Φ such that

⃗ ⃗

Φ(α) > ϑ, Φ(α) > α,$B_{q}$(d, β) < Φ(α) (max β ≤ α).

Include the initial single-model requirements in this finite register. The formulas defining its members have already been fixed. No partial truth construction, and no bound on a variable formula’s complexity, is being used here.

For a definable class A of ordinals write

Lim(A) = {λ: sup(A ∩ λ) = λ > 0}, Cl(f) = {λ: ∀α < λ f (α) < λ}.

Multiple ordinal inputs can be replaced by their maximum in the closure condition. Define

$G_{0} =${µ: µ is a strong limit cardinal, cf(µ) = ω, µ ∈ Cl(Φ)}, \

$G_{j+1} = G_{j} ∩ Lim(G_{j})$(j < ω),$G_{ω} =$j<ω$G_{j}.$

Because Φ(0) > ϑ, every member of every$G_{j}$exceeds the common parameter cutoff. This detail cannot be replaced by discarding an arbitrary initial segment after each new template choice.

The hierarchy itself has a uniform definition. For an ordinal λ, form$A_{0} = G_{0} ∩$(λ + 1) by Separation and then, by finite recursion on subsets of λ + 1, put

$A_{i+1} =${β$∈ A_{i}: β > 0$and$sup(A_{i} ∩$β) = β}.

The assertion$λ ∈ A_{j}$is one formula with j, λ as inputs, and is equivalent to$λ ∈ G_{j}.$Quantifying over j ∈ ω defines$G_{ω}.$In particular the countable constructions below can choose least witnesses using this formula and Replacement.

Lemma 13.4 (Closure and absorption). Each$G_{j}$is unbounded and closed under suprema of strictly increasing countable sequences of its members. The class$G_{ω}$is unbounded. If a current eligible class S contains$G_{j},$and a finite sequence of refinements consists of the bound closures and thresholds in the fixed register and restrictions to limit points of earlier eligible classes, then the resulting class contains$G_{j+m}$for some finite m. Here every used bound must have a witness under its stated hypotheses.

Proof. Given any starting ordinal, choose strictly increasing infinite cardinals$(κ_{n})_{n<ω}$above it with$κ_{n+1} >$max$2^{κ_{n}},$sup{Φ(α):$α < κ_{n} }.$

The supremum κ of this sequence is a cardinal of cofinality ω. For every cardinal λ < κ, some$κ_{n}$exceeds λ, and then$2^{λ} ≤ 2^{κ_{n}} <$κ. For every α < κ, the same choice gives Φ(α)$< κ_{n+1} <$κ.

Thus$κ ∈ G_{0}.$If instead the$κ_{n}$are an increasing sequence in$G_{0},$their supremum is again a countable-cofinality strong limit cardinal and is strictly Φ-closed by these same two tests. This proves the two assertions for$G_{0}.$

Suppose they hold for$G_{j}.$Above any starting ordinal choose a strictly increasing countable sequence in$G_{j}.$Its supremum belongs to$G_{j}$by closure and to$Lim(G_{j})$because the sequence is cofinal there. This proves unboundedness of$G_{j+1}. A$countable increasing sequence in$G_{j+1}$has its supremum in$G_{j},$and its own members witness that this supremum belongs to$Lim(G_{j}).$Hence$G_{j+1}$has the asserted closure as well.

Choose$λ_{n} ∈ G_{n},$strictly increasing and above an arbitrary prescribed ordinal. For each fixed j, its tail lies in$G_{j}$because the classes are nested. The supremum belongs to$G_{j}$by its countable closure. It consequently belongs to$G_{ω},$proving unboundedness.

For absorption, maintain that the current eligible class contains a particular$G_{k}. A$request value on inputs below a member µ$∈ G_{k}$is less than Φ(α) for a suitable α < µ, and hence less than µ. Thus a bound-closure refinement retains all of$G_{k}. A$constant threshold is included as a request with input 0 and has the same property. If the next refinement demands cofinally many members of the current class below the new level, retain$G_{k+1}:$its members are limit points of$G_{k}$and thus of the current class. If several earlier eligible classes are mentioned, the maintained index can first be increased to the maximum of their finitely many indices. Induction through the finite refinement list proves the claim, with m bounded by its number of limit-point refinements.

Theorem 13.5 (Common levels for all finite depths). With the fixed data of either application and the constructions proved in the preceding sections, there is an unbounded class of countable-cofinality strong limit cardinals at which all its finite-depth conclusions hold simultaneously. In the marked application this includes the working packages, projection and type correspondences, amalgamated completion, and exact boundary lifting for every$C_{n},$uniformly over the root prescription codes realized at arbitrarily large eligible single-model levels. In the geometric application it includes categoricity, the working packages, basis lifting, and exact boundary lifting for every finite shape. One such common level may be chosen above any specified set of fixed cardinal thresholds.

Proof. Use the fixed register and Φ just constructed. The initial single-model results hold on$G_{0}$after the initial requirements have been included. Suppose the assertions required as input to a finite induction step hold throughout$G_{j}.$Take S to be the class defined by their unary adequacy formula, with the current descriptor. It contains$G_{j}.$Lemma 13.2 supplies the mixed conditions for that step. Lemma 13.3 identifies its bound requests and gives the existence of each relevant witness at its place in the proof. Lemma 13.4 then retains some$G_{j'},$with j' < ω, through all its refinements.

When a marked step extracts a new template, its code lies in the fixed descriptor set by Proposition 13.1. The remaining requests with that code as parameter were already majorized by Φ. Thus making the choice introduces no new closure function or cutoff. For a given finite shape, the finitely many previously required lower shapes can first be brought to one$G_{j}$by taking the largest of their indices. The same observation applies to the finite projection lists in the marked argument. The two ordinary finite inductions therefore give, for each finite descriptor, all its required conclusions on$G_{j}$for some finite j.

In the marked application only root codes consistent at arbitrarily large eligible single-model levels are used. A code obtained from an actual pair at a sufficiently closed starting cardinal has that property: freely lift its type with the named approximation data to arbitrarily large single-model levels. The majority rule is preserved there, and restriction from such a level gives the same stationary prescription at every sufficiently closed smaller single-model level with that named pattern. This is the prescription argument in Lemma 10.8, prior to the use of the finite marked systems. It requires no persistence of a no-growth statement about P at larger levels. The fixed code set and majorant include every such possible input code, so the common-level construction can precede the choice of the actual pair.

Every member of$G_{ω}$belongs to$G_{j}$for every finite j. It consequently satisfies the conclusion for every finite descriptor used in the application, although the index j and the selected template may depend on that descriptor. Lemma 13.4 makes$G_{ω}$unbounded, so choose a member above the desired thresholds. All constructions in this argument are ordinary set recursions, Separation, Replacement, and finite induction with uniform formulas. This completes the simultaneous closure justification in ZFC.
