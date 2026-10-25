# 4 Stable diagrams and amalgamation at closed levels


Throughout this section, K is the AEC fixed after Proposition 2.3: it is categorical in unboundedly many cardinals, and ℓ = LS(K). We use the order presentation E of Theorem 2.6. A tuple may have any set as its index set. Comparisons between tuples always specify the identification of their index sets. Reindexing by an ordinal, padding, and repetitions do not change any of the arguments below.

The goal is to turn bounded-tuple reversal into amalgamation at selected levels. We first stabilize tuple comparisons across categoricity sizes, then use the order presentation to test and realize those comparisons over an entire base. Amalgamation will be a conclusion of this process.

## 4.1 Stabilization of strong-map classes

Fix an infinite cardinal σ. At a categoricity cardinal κ > ℓ + σ where Theorem 3.11 holds for σ-tuples, put

(M, a) ≡σκ (N, b) ⇐⇒ some strong map f: M −→ N satisfies f (a) = b.

Here ∥M ∥ = ∥N ∥ = κ, and the lengths of the displayed tuples are at most σ. This is an equivalence relation. Reflexivity is immediate. Categoricity allows one to regard all the maps as maps between copies of one model; reversal then gives symmetry, and composition gives transitivity. Using structures with universe κ, or one fixed representative and its tuples, its classes form a set. Their number, for all the tuple lengths under consideration, is bounded by the fixed cardinal supplied by Lemma 3.6. Denote an infinite such bound by$B_{σ}.$It depends on ℓ, σ, not on κ.

Lemma 4.1 (Canonical classes above one categoricity size). For ∥N ∥ ≥ κ, a tuple a in N has a well-defined ≡σκ-class: compute it in any strong κ-submodel containing a. Strong embeddings between models of size at least κ preserve this class.

Proof. The downward LS axiom supplies the submodel, after adding κ many elements to the requested set if necessary. If$M_{0}, M_{1} ≤_{K} N$are two such submodels, apply LS to$|M_{0} | ∪ |M_{1} |.$It gives$M_{2} ≤_{K} N$of size κ containing both. Coherence gives$M_{i} ≤_{K} M_{2}.$The two occurrences of a therefore have the same class. For a strong embedding f: N → N', the image of a witnessing submodel is a strong κ-submodel of N', so the same observation proves preservation. All these comparisons take place inside a given ambient model; no amalgamation property is used.

Proposition 4.2 (Stable diagrams). There is a definable, nondecreasing cardinal function t, with t(σ) > ℓ + σ a categoricity cardinal for every infinite σ, having the following properties.

1. Tuples of length at most σ in models of size at least t(σ) have canonical diagrams. Equality of diagrams is preserved by every strong embedding between such models, and there are at most$B_{σ}$diagrams at these lengths.

2. Diagrams include atomic diagrams, respect reindexing and restriction, and are compatible when the bound σ is increased. We denote equality by D(a; M) = D(b; N), suppressing the bound when it is understood.

3. If κ ≥ t(σ) is a categoricity cardinal, equality of diagrams between tuples in κ-models is implemented by a strong map between those models.

4. A possible diagram of a pair of tuples (a, c), of total length at most σ, can be realized over any tuple with the diagram of a in any categoricity model of size at least t(σ). “Possible” means that the diagram occurs in a model in the domain of its definition.

Proof. If γ ≥ κ are categoricity cardinals above the reversal threshold, Lemma 4.1 associates a κ-class to every γ-class. This gives a projection$π_{γκ},$and these projections compose. They are surjective. Indeed, a κ-model is isomorphic to E(I) for |I| = κ; extend I to an order of size γ and use the strong order map. Every tuple class in the smaller model then occurs in the larger one. This argument supplies the needed extension without a no-maximal-model assumption.

These projections are eventually all bijective. Otherwise, construct a sequence of categoricity cardinals with more than$B_{σ}$successive noninjective projections, and choose one final categoricity cardinal ρ above the entire sequence. For each noninjective projection, surjectivity supplies a pair of ρ-classes which agree when projected to the earlier stage and differ when projected to the later stage. Pairs selected at distinct stages are distinct: after a pair has separated it remains separated under every later refinement. This gives more than$B_{σ}$pairs from a set of size at most$B_{σ}, a$contradiction. The construction uses only a set-length sequence of cardinals and choices from sets.

Choose a categoricity cardinal$c_{σ}$beyond this stabilization and reversal threshold. The canonical$c_{σ}-class$defines the desired diagram on models of size at least$c_{σ}.$The bijective projections show that its equality can equally be computed at every later categoricity cardinal. If two tuple bounds are used, compare them at a categoricity cardinal above both thresholds. Restriction of strong maps then gives the same restricted equivalence. Atomic formulas and their negations are preserved because strong maps are structure embeddings.

For definiteness, thresholds can be chosen as least cardinals having the stated eventual properties. Choose t(σ) to be the least categoricity cardinal strictly above ℓ + σ and above all the thresholds$c_{τ}$for infinite τ ≤ σ. This is a nondecreasing definable function. The preceding arguments prove the first three assertions.

For the fourth, first put a realization of (a, c) into a strong$c_{σ}-submodel.$If the originally chosen ambient size is smaller than a desired target categoricity size, this categorical submodel can be extended to that size by the order presentation. If the original ambient size is larger, LS gives a submodel of the desired size containing the realization. Thus the joint diagram has a realization in a model of the target categoricity size. Apply the third assertion to the first tuple and the specified tuple in the target. The resulting strong map transports the whole realization as required.

Proposition 4.3 (Categoricity at countably cofinal closure points). Suppose ζ > ℓ is an infinite cardinal of countable cofinality and

t(σ) < ζ for every infinite σ < ζ.

Then K is categorical in ζ. Moreover any diagram match between bounded tuples in two ζ-models extends to an isomorphism between those models. Here and throughout the paper, bounded at a level means of cardinality strictly less than that level.

Proof. Existence follows from E(I) for |I| = ζ. Let M, N have size ζ, and choose countable increasing exhaustions of their underlying sets by sets of size less than ζ. Start with the prescribed bounded diagram match, or with the empty match. At a forward step, enumerate together the current source tuple and the next part of the exhaustion of M. Its length and the length of the current target tuple are bounded by an infinite σ < ζ. Put the data on each side inside a strong submodel of size t(σ) < ζ. Their current tuples have the same diagram. Proposition 4.2 gives a strong map of these submodels matching those tuples. Its values on the new entries extend the match, and the enlarged tuples again have equal diagrams. At the next step interchange M, N.

Only finitely many previously chosen bounded tuples are used at each step, so their combined length stays below ζ. The union of the countable sequence of partial matches is a bijection |M | → |N |. Every finite tuple and every value of a finitary function occur at some step, where the atomic diagram is preserved. The bijection is therefore a structure isomorphism.

The closure cardinals in Proposition 4.3 are unbounded. For example, starting above any specified cardinal, choose a strictly increasing sequence$(α_{n}: n <$ω) such that$α_{n+1}$exceeds all t(σ) for$σ ≤ α_{n}.$Its supremum has the required closure and countable cofinality. Including$2^{α_{n}}$in these requirements makes the supremum a strong limit. We will use these stronger closure points below.

## 4.2 Natural diagrams and interchange of blocks

Definition 4.4 (Natural and placed diagrams). Consider a set-sized list of terms in an order presentation. Each term consists of a label and an increasing finite list of positions. Extend the order to size at least the threshold for the list and compute its diagram there. The result is its natural diagram. If A = E(I), a placement of an additional tuple d over A is a labeled representation in an order extension of I, retaining the positions and chosen representations of the parameters in A. Its placed comparison over A is the natural diagram of (d,$a_{A}),$where$a_{A}$is a fixed enumeration of A.

The natural diagram is independent of the extension used. Indeed, linear orders amalgamate over a common suborder: for each cut of the suborder, place the remaining portions of the two orders in that cut while preserving each portion’s order. Extending the amalgam further if necessary gives a common sufficiently large presentation. Strong order maps and Proposition 4.2 identify the two diagrams. The same argument shows that only the labels and the joint order/equality pattern of their supports matter. All diagrams with parameters use matching parameter enumerations. One may instead list all labels on the base order, allowing repetitions: restriction gives an enumeration of the elements, and reinserting the repetitions is forced by their equalities.

A placed comparison over a whole µ-model is evaluated in a sufficiently large presentation. It is not, by this definition, an assertion that the original µ-model itself lies above the threshold for diagrams of length µ.

Lemma 4.5 (Orbits over parameters). Let σ be infinite and suppose

$χ^{σ} =$χ,$χ ≥ ℓ + 2^{2^{σ}}.$

At every sufficiently large categoricity cardinal, there are at most χ automorphism orbits of σ-tuples over any specified set of at most χ parameters.

Proof. Present the categoricity model as E(H(δ)), choosing |δ| to be its cardinality and cf(δ) > χ. This is possible at every sufficiently large cardinal, including singular cardinals. Fix term representations of the parameters, and let S ⊆ H(δ) be their support set. Its size is at most χ. Every member of S is coded by a finite list of ordinals and integer and rational coefficients. The union of its ordinal supports consequently also has size at most χ.

For one further position, its finite ordinal support has at most χ possible order/equality patterns over these old ordinal supports. The discrete coefficients contribute only countably many choices for each finite code. Such a pattern determines all comparisons of the new position with S. For at most σ new positions, include their mutual comparisons, their identifications with old positions, and the term labels. There are at most$χ^{σ} = χ$choices so far.

To apply Theorem 3.5, also record which strict slots over the old and new positions are realized in H(δ). The old support S is fixed. A slot over S not containing a new position is unchanged. At most σ old slots contain new positions, and inside each there are at most$2^{σ}$cuts of the new support to test. The new flags therefore have at most$2^{2^{σ}} ≤ χ$possible values. The full record has at most χ possibilities.

The combined list of old and new positions has size at most χ < cf(δ). Theorem 3.5 extends equality of full records to an order automorphism fixing S pointwise. Its induced automorphism of the presentation fixes the parameters and matches the tuples. Thus the number of structure-automorphism orbits is at most the number of records.

Lemma 4.6 (Disjoint block transpositions). Take two set-sized families of labeled terms. In disjoint convex regions of their joint support order, suppose each region consists of two adjacent blocks, one used only by the first family and one only by the second. Interchange the blocks in every such region, retaining their internal orders and all positions outside the regions. The joint natural diagram is unchanged.

Proof. Suppose the original and modified diagrams were different. Let σ bound the two lists, their supports, and the shared positions. Choose$χ ≥ ℓ + 2^{2^{σ}}$with$χ^{σ} =$χ, for instance by taking a sufficiently large power of two.

In each region repeat the pair of blocks along an arbitrary linear order L. If the first family’s block was on the left, use the order L for the repetitions; if it was on the right, use the reverse of L. Write$d_{i}$for the first-family tuple using the blocks at index i, and$e_{j}$for the second-family tuple using the blocks at index j; retain all the shared positions outside the regions. For i < j, the diagram of$(d_{i}, e_{j})$is the original one, and for i > j it is the modified one. Comparisons within either family and across distinct regions do not change.

Let ϵ be the least infinite cardinal satisfying$2^{ϵ} >$χ. The binary tree$2^{<ϵ}$has at most χ nodes: for α < ϵ each level has size at most χ, and ϵ ≤ χ. Give it lexicographically ordered divider points, one between the two successor subtrees at each node. Explicitly, encode branch digits by −1, 1, and encode the divider at a node s by the sequence s followed by 0, using −1 < 0 < 1 in lexicographic comparison. Adjoin one point for every branch in$2^{ϵ}.$Distinct branch points determine distinct strict cuts over the divider points. Use this as the order L.

The tuples$e_{j}$at the divider indices, together with the fixed shared data, use at most χ parameters. If two branch-indexed tuples$d_{i}$were in the same automorphism orbit over these parameters, their diagrams with every divider tuple would agree. A divider between the two branches gives the two different diagrams, a contradiction. Hence there are more than χ such orbits. Pad the constructed order to a sufficiently large categoricity size and apply Lemma 4.5. This is impossible.

## 4.3 Bounded tests over a well-ordered presentation

The next elementary set-theoretic observation will also be used for the more elaborate layouts of later sections.

Lemma 4.7 (Ordinal-vector witnesses). Let C be a set, and let U be a definable class of functions C → Ord, with fixed set parameters allowed in its definition. There is a set$U_{0} ⊆ U$such that each u ∈ U dominates some$v ∈ U_{0}$coordinatewise.

Proof. The assertion is immediate if C is empty or U is empty. Well-order C, and suppose no such set exists. For every ordinal β, the set$U ∩ V_{β}$fails to generate U upwards. There is therefore an element of U which dominates none of its members. Let h(β) > β be the least ordinal such that one such witness lies in$V_{h(β)}.$This is a definable ordinal function.

Take an ordinal length λ satisfying the partition relation for pairs, |C| colors, and an infinite homogeneous set, supplied by Lemma 2.5. Define increasing ordinals$β_{i},$for i ≤ λ, recursively, with$β_{i+1} > h(β_{i})$and with limit values above all earlier values. Choice for a set-indexed collection of nonempty subsets of$V_{β_{λ}}$now selects witnesses$u_{i}$which dominate no member of$U ∩ V_{β_{i}},$for i < λ. For i < j, we have$u_{i} ∈ V_{β_{j}},$so some coordinate satisfies$u_{i}$(c)$> u_{j}$(c). Color the pair i < j by the first such coordinate in the fixed well-order of C. An infinite homogeneous set yields an infinite strictly decreasing sequence of ordinals in that coordinate. This contradiction proves the claim. The rank bounding above ensures that only ordinary set-sized Choice, not a choice principle for proper classes, was used.

Proposition 4.8 (Uniform testing of placed comparisons). There is a definable nondecreasing infinite cardinal function g, depending on K and its fixed presentation, such that the following holds. If I is an infinite well-order, A = E(I), and two placements of a tuple of length at most σ have different placed comparisons over A, then their natural diagrams already differ over a subset of A of size at most g(σ). The bound is independent of |I|.

Proof. Amalgamate the two support orders over I, and let T be the union of the supports of the two added tuples. Its size is at most σ. Freeze its order, the labels and supports of the two tuples, and the subset of its positions which belong to I. Up to a relabeling on a fixed set of size at most σ, these frozen data range over a set.

For fixed frozen data, each component of I \ T in a strict slot over T is well-ordered. Record its ordinal length. The set of slots is fixed, so these lengths form an ordinal vector. Restrict attention to the vectors that give valid configurations and for which the two placed comparisons are unequal. This is a definable class: order presentations and diagrams are defined from set codes, and diagrams of any specified set length can be evaluated above their thresholds.

Coordinatewise domination gives an order embedding of the smaller configuration into the larger one, fixing T and preserving the base positions. Natural diagrams respect these embeddings. Thus a valid smaller unequal configuration remains a witness in any dominating valid configuration. Apply Lemma 4.7 to this class, obtaining a set of valid witnesses. Equivalently one could apply it to the upward closure and select its generators from valid configurations; no assertion that arbitrary vectors themselves describe well-orders is required.

Bound the sizes of the base orders in this set of witnesses. An embedded witness uses only that bounded number of old positions. All labels on these positions give at most their cardinality plus ℓ elements of A, and the diagrams of the two added tuples with these elements are unequal. Taking a cardinal bound over the set of frozen data gives g(σ). Increasing it to an infinite nondecreasing function causes no change in the assertion. When a witness uses only finitely many positions, “all labels” simply means their evaluated terms; no assertion about membership of a finite-order presentation in K is needed.

Proposition 4.9 (Compact placement). Let A = E(I), where I is an infinite well-order, and let χ > ℓ + σ satisfy$χ^{σ} =$χ. Suppose that for every X ⊆ A of size at most χ a possible joint diagram$q_{X}$(d, X) is prescribed, where d has length at most σ. Assume these prescriptions restrict coherently and that their parameter diagrams are the natural ones of X. Then one placement of d over I realizes all the prescriptions.

Proof. Fix one term representation per parameter in A. Write$S_{X} ⊆ I$for the supports of X. For one set X, its prescription has a placement. To see this, extend I to a sufficiently large categoricity size and use Proposition 4.2 to realize the possible joint diagram over the actual parameter tuple. The realization has term representations in that presentation.

A support profile over X records the labels for d, its formal support order$T_{0}$of size at most σ, and comparisons and coincidences with$S_{X}. A$well-order of size at most χ has at most χ cuts. Hence there are at most$χ^{σ} = χ$profiles. The positions of$T_{0}$in one strict slot over$S_{X}$form a cluster. Each profile has a continuation over I which leaves every such cluster intact: insert the cluster at a single cut of I extending its specified cut over$S_{X}.$

Call a hit of a new parameter support on$T_{0},$or the separation of two positions in one cluster by a new parameter support, a new event. For X' ⊇ X, all continuations of a profile with no new event over$S_{X'}$have the same natural diagram over X'. Within each old slot, the whole cluster can only change its position across a block of new parameter positions. The slots are disjoint, so Lemma 4.6 applies simultaneously.

Suppose no placement solves all the prescriptions. Start with any$X_{0}$of size at most χ. Given$X_{i},$choose for every profile over$X_{i} a$continuation with no new event over all of I. It fails a prescription on some set of at most χ parameters. Adjoin one such failing set for each profile to obtain$X_{i+1}.$At limits take unions, and carry out$σ^{+}$stages. Every set constructed, including S

$X_{∗}$Take= i<σa$+placementX_{i},$has sizerealizingat$mostq_{X_{∗}}$χ,. Atbecauseeach$stageσ^{+} ≤$itsχ. profile over$X_{i}$was considered. If it had no

new event between$S_{X_{i}}$and$S_{X_{i+1}},$the preceding no-event comparison would identify its diagram on the selected failing set with that of the chosen continuation. This contradicts its realization of$q_{X_{∗}}.$Thus it has a new event at every stage. A support position can be newly hit only once, and a pair can be newly separated only once. There are at most$σ + σ^{2} = σ$such events. They cannot occur at$σ^{+}$different stages.

Lemma 4.10 (Unique lifts of bounded diagrams). Let µ > ℓ be a strong-limit cardinal of countable cofinality strictly closed below itself under t and g. Let$A ≤_{K} B$have size µ, and identify A = E(I) for a well-order I of size µ. For a tuple d in B of length at most σ < µ, the diagrams

D(d, X; B), X ⊆ A, |X| < µ,

lift to one placed comparison over all of A, uniquely as a comparison diagram. Restricting a lifted tuple gives the lift of its restricted diagram.

Proof. The displayed bounded diagrams are defined, since their thresholds lie below µ, and they agree on the parameters with the natural diagrams. For every sufficiently large χ < µ with$χ^{σ} =$χ, Proposition 4.9 gives a placement realizing the tests of size at most χ. Such χ are cofinal below µ: use$χ = 2^{α}$for σ ≤ α < µ, enlarging α as necessary.

Once χ ≥ g(σ), any two resulting placements have the same full comparison by Proposition 4.8. Fix one of them. Every bounded test is covered by a larger choice of χ, whose placement has that same full comparison. The fixed placement consequently realizes every bounded test. The same argument gives uniqueness. A restriction realizes the restricted tests and hence, by uniqueness, is their lift.

## 4.4 Amalgamation and type counts

Theorem 4.11 (Amalgamation at closed levels). There is an unbounded class of strong-limit cardinals µ of countable cofinality with the following properties.

1. K is categorical in µ, and any two µ-sized strong extensions of a µ-model have a strong amalgam of size µ.

2. If$A ≤_{K} B_{0}, B_{1}$all have size µ, and$d_{i} ∈ B_{i}$are tuples of the same length at most σ < µ, there is such an amalgam identifying$d_{0}$with$d_{1}$if and only if

$D(d_{0},$X;$B_{0}) = D(d_{1},$X;$B_{1})$for every X ⊆ A, |X| ≤ g(σ).

3. There are at most µ singleton types over each µ-model, where type means identification in an amalgam over that model.

One may take every sufficiently large strong-limit cardinal of countable cofinality strictly closed under t and g.

Proof. Such levels are unbounded by the countable closure construction following Proposition 4.3. Categoricity at them has already been proved. Identify a given base with A = E(I), where I is a well-order of size µ. Extend I to an order J whose cardinality γ is a categoricity cardinal at least t(µ), and let G = E(J). Thus A is strongly included in its specified position in G.

We show that every µ-sized strong extension B of A embeds strongly into G over A. Choose$M_{n} ≤_{K}$B, increasing with union B, with$∥M_{n} ∥ <$µ. This follows by LS from a countable exhaustion of B, containing the preceding submodel at each step; coherence makes the chain strong. Choose compatible enumerations$d_{n}$of these models, so that each earlier list is a sublist of the next.

Lemma 4.10 assigns coherent placed comparisons to$(d_{n},$A). Each is realized over A in G, and the realizations can retain the previous assignments. More explicitly, realize the corresponding term pattern in an order extension of size γ. Its parameter tuple A, and then its tuple (A,$d_{n−1}),$have the same diagram as the already assigned ones. Their length is at most µ, so Proposition 4.2 at γ ≥ t(µ) supplies the strong map realizing the new list while fixing these previous data.

It remains to verify strongness of the copied small models; atomic agreement by itself would not suffice. Fix n, and bound the length of$d_{n}$by an infinite$σ_{n} <$µ. Choose the categoricity cardinal$ρ = t(σ_{n}) <$µ. LS puts the original enumeration inside$B_{n'} ≤_{K} B$of size ρ, and the copied enumeration inside$G_{n'} ≤_{K} G$of that size. Coherence gives$M_{n} ≤_{K} B_{n'}.$The copied and original lists have the same bounded diagram; Proposition 4.2 gives a strong map$B_{n'} → G_{n'}$with exactly the prescribed values on$d_{n}.$Its restriction shows that the copied$M_{n}$is a strong submodel of G.

The copied models are nested, and coherence makes their inclusions strong. Their union is a strong submodel of G by the chain and common-upper-bound axioms. It is the image of an embedding of B. Every element of A eventually occurs in some$d_{n},$and its equality with that parameter is part of the lifted comparison. The embedding therefore fixes A. Performing this construction for$B_{0}, B_{1}$in the same G gives an amalgam. LS supplies a strong µ-submodel of G containing both images; coherence makes it a strong amalgam of the required size.

For the second assertion, any identifying amalgam preserves the displayed bounded diagrams, giving necessity. Conversely, Proposition 4.8 identifies the placed lifts of$d_{0}, d_{1}$over A. Realize this common lift once in G. On each side start the preceding countable construction with the specified tuple already assigned, and choose every small-model enumeration to contain that tuple. Homogeneity over A and the old assignments works exactly as above. The two resulting embeddings identify the tuples, and the same LS shrinking applies.

For a singleton, a placement uses one label on a finite support. Relative to the well-order I, each support position is either an old position or lies in one of its |I| + 1 cuts. Together with the finitely many mutual comparisons and the label, these data have at most µ possibilities. They determine the full natural comparison. The second assertion identifies exactly the types with equal comparison, proving the bound.

Amalgamation has thus been obtained at the stated levels from the AEC axioms and unbounded categoricity. We have not assumed that all models of intermediate cardinalities amalgamate. The next section records precisely the level-by-level properties that will be required of later categories of finite systems.
