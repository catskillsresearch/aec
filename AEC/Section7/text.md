# 7 Isolation and dominated extensions


Throughout this section, C is a working scheme in the sense of Definition 5.2. We use the refinements of the eligible levels required in Section 6. All objects and extensions in a displayed type are at one eligible level, unless a change of level is stated. We retain the eligible-subclass hypothesis of Convention 5.3; every larger auxiliary sufficiently closed level below is chosen in its unbounded refined subclass. A type over an object at a smaller eligible level is computed in a section of that level; Corollary 6.7 makes this independent of the section. A tuple is bounded when its cardinality is less than the level of its base. We write$p_{B^{fr}}$for the free lift$p^{B}$of Theorem 6.10 when its role needs emphasis.

We will repeatedly use the following convention concerning bounds. A request involving a tuple of cardinality σ is first enlarged to an infinite arity at least σ. The testing, compact-placement, and approximation bounds of Section 6 are then applied at that arity. There are only finitely many such enlargements in each argument below. A source level is required to be strictly closed under those bound functions. Thus, when a tuple is bounded at a smaller level, every test used to determine its type may be taken below that smaller level, even if the receiving object is at a much larger eligible level. This does not assert saturation over an unbounded parameter set.

Our goal is an extension controlled by a given mark, with an embedding into every ambient object realizing that mark’s type. Relative isolation will give this control on bounded tuples. The main existence argument first treats one bound on tuple length and then obtains all bounded lengths in a single extension.

## 7.1 Relative isolation

Definition 7.1. Let q = tp(u, c/A) and p = tp(u/A), where the concatenation (u, c) is bounded. We say that q is isolated relative to u if there is a bounded set Z ⊆ A such that, for every q' = tp(u', c' /A),

tp(u' /A) = p and D(u', c', Z) = D(u, c, Z) =⇒ q' = q.

Here and below a parameter set in a diagram is supplied with a fixed enumeration, and the same enumeration is used on both sides. We call Z an isolating fragment. A projection retains the entire tuple u unless explicitly stated otherwise.

Lemma 7.2. The following hold at sufficiently closed eligible levels.

1. A projection of a relatively isolated type is relatively isolated.

2. Suppose A ≤ B, q = tp(u, c/A) is isolated relative to u, and an actual coupling over B satisfies tp(u/B)$= tp(u/A)_{B^{fr}}.$

Then tp(u, c/B)$= q_{B^{fr}}.$

Moreover this type is isolated relative to u, using the same isolating fragment as q.

The second assertion also holds when A is at a smaller eligible level than B, provided (u, c) and the required uniform bounds are below the level of A.

Proof. For the first assertion, write$c = (c_{0}, c_{1})$and let Z isolate q. Suppose (u',$c_{0'})$has the prescribed marginal on u and the same diagram as (u,$c_{0})$over Z. In a model containing A, u',$c_{0'},$bounded saturation extends this diagram by a tuple$c_{1'}$so that

D(u',$c_{0'}, c_{1'},$Z) = D(u,$c_{0}, c_{1},$Z).

Isolation identifies the full type over A, and its projection identifies tp(u',$c_{0'}$/A).

For the second assertion, fix an isolating fragment Z. It is enough to compare the actual joint type over B with$q_{B^{fr}}$on the uniform testing arity for (u, c). Enlarge that arity to include Z and choose approximation lists in A for both q and p = tp(u/A), long enough to evaluate all the comparisons just specified. Let t be a test tuple from B at this enlarged arity. Bounded saturation moves t to a tuple t' in A, preserving its diagram over Z and both approximation lists.

Choose a realization$u_{0}$of p over A. The free evaluation of p gives

D(u, t, Z)$= D(u_{0},$t', Z).

Saturation over the bounded list$(u_{0},$t', Z) supplies$c_{0}$such that

$D(u_{0}, c_{0},$t', Z) = D(u, c, t, Z).

In particular$(u_{0}, c_{0})$agrees with q on Z and has marginal p. Isolation gives$tp(u_{0}, c_{0}$/A) = q. Consequently the actual answer to the query t is the answer that q gives to t'. Because the query was moved over the approximation list for q, that is also the free evaluation of q on t. The testing theorem identifies the types over B.

Now let a competing type over B have the same marginal on u and agree with the displayed type on Z. Its restriction to A is q. The argument just given identifies it with$q_{B^{fr}},$proving isolation there. In the mixed-level case, perform these comparisons at the uniform test bound below the source level. Mixed realization supplies the required sections, and the same argument applies to those diagrams.

Proposition 7.3. There is a bound function h, depending only on the fixed working scheme, with the following property. Put σ = |u, c|$+ ℵ_{0}.$At sufficiently closed eligible levels, precisely one of the following alternatives holds for q = tp(u, c/A):

1. q is isolated relative to u by a fragment of size at most h(σ);

2. there are an extension A ≤ B at the same level and an extension$q_{B}$of q such that

$q_{B}$̸=$q_{B^{fr}}, q_{B}$↾$u = tp(u/A)_{B^{fr}}.$

In particular, every relatively isolated type has an isolating fragment bounded by h(σ), uniformly in the level and in the type.

Proof. Choose an infinite χ large enough for the testing theorem at arity σ, for the approximation lists for q and its marginal p, and for the finitely many joint comparisons made below. These choices are uniform in σ. Increasing χ if necessary, all the supports in the chosen approximation lists have cardinality at most χ.

Present A = F (I) on a well-order of the level cardinality µ. We may choose I to have more than σ disjoint consecutive blocks, each of order type and cardinality µ: this is still a well-order of cardinality µ, and all such presentations are objects at this level. Let$J_{0}$consist of the supports of the approximation lists, together with an initial segment of order type$χ^{+}$in every candidate block. Its size has a bound depending only on σ. Let$Z_{0}$be the set of all term values on$J_{0}.$Since the label set is fixed, the same is true of$|Z_{0} |.$

If$Z_{0}$isolates q, we have the first alternative. Suppose it does not. Choose$q^{1}$̸=$q^{0} = q$with the same marginal p and the same diagram on$Z_{0}.$By Lemma 6.4, give both types placements over the displayed presentation of A, and amalgamate their support orders over I. The combined new support has cardinality at most σ. Each new support position either hits the interior of one candidate block or determines an interior cut of at most one such block. We can therefore choose a candidate block J whose interior contains neither a hit nor a cut of either placement.

Set$A_{∗} = F (J_{0} ∪$J) ≤ A. This object has cardinality µ. The restrictions of$q^{0}$and$q^{1}$to$A_{∗}$are equal. To check this, take a test at the fixed sufficient arity. Move every position of the test lying in J into the initial$χ^{+}$part of J, preserving the order and equality pattern of the test. This can be done above any positions of that initial part which need to remain in the pattern: fewer than$χ^{+}$positions have been specified. Leave the positions outside J unchanged. No position of either candidate separates the interior of J, so the move preserves the natural diagram with either candidate. The moved query uses only$J_{0}$and therefore has the same answer for$q^{0}$and$q^{1}.$The testing theorem proves equality over$A_{∗}.$

The approximation lists for$q^{0}$and p lie in$A_{∗}.$Their majority evaluations show that$q^{0}$and p over A are free from$A_{∗}.$Also, an isomorphism f:$A_{∗} ≃ A$may be chosen to fix those bounded lists, by bounded diagram homogeneity. The transport assertion for free types then gives

$f q^{0}$↾$A_{∗} =$q.

Transport the inclusion$A_{∗} ≤ A$along f, viewing its larger object as an extension B of the original base A. Transport$q^{1}$as well. Its restriction is q because the two restrictions to$A_{∗}$agree. Its marginal is the free lift of p. Its joint type is not free, since the unique free lift before transport was$q^{0},$distinct from$q^{1}.$This is the second alternative.

Choose h(σ) to bound the size of$Z_{0}$for these uniform choices. Lemma 7.2 excludes the second alternative when q is isolated, even if an initially given isolating fragment was larger. This proves both exclusivity and the asserted uniform bound.

## 7.2 Primeness and descent of isolation

Definition 7.4. Let X ≤ Y be same-level objects and let b be a bounded tuple in Y. We say that Y is all-dominated over X + b if, for every bounded tuple c from Y, the type tp(b, c/X) is isolated relative to b.

The quantifier over all bounded tuples is part of this definition. It is not enough to verify isolation for individual entries, or for the tuples in one chosen countable exhaustion of Y.

Proposition 7.5. Let Y be all-dominated over X + b at a sufficiently closed eligible level µ.

1. If an extension N of X contains a tuple b' of the same type over X, there is an arrow Y −→ N over X sending b to b'. The target may be at a larger eligible level. A prescribed bounded tuple match can be retained whenever its joint type with b over X already agrees.

2. Two all-dominated objects over the same data X + b are isomorphic over those data. The isomorphism may retain a prescribed bounded tuple match of the kind just described.

3. In an actual coupling, if a bounded tuple x has product with b over X, then tp(x/Y) is free from X.

Proof. Choose increasing bounded lists$c_{n}, n <$ω, exhausting Y; include b, the prescribed initial data, and exhaustions of every vertex by smaller strong submodels. Suppose the image of$c_{n}$has already been chosen with the correct full type over X. Let$Z_{n+1} ⊆ X$isolate tp(b,$c_{n+1}$/X). The old image and the source list have the same diagram over$Z_{n+1}.$Saturation in N extends this bounded match to (b,$c_{n+1}, Z_{n+1}).$Relative isolation makes its full type over X correct. Taking the union gives a map on all of Y fixing X: whenever an entry of X occurs in a list, its equality with the corresponding parameter is part of its full type. The strong-submodel exhaustions and the map criterion in the working package show that this map is an arrow. This proves the first assertion, also into a larger target because every saturation request is bounded at the source level.

For the second assertion, perform the same construction alternately on the two sides, at each step including the next list in the chosen exhaustion on the side to be covered. Both objects have isolation for the enlarged bounded list. The construction therefore continues in both directions and its union is an onto structural isomorphism.

For the third assertion, use symmetry and the definition of product to choose a model W ≥ X containing x over which b is free from X. Type-identifying amalgamation brings W and the actual coupling into a common extension, identifying x and b over X. For every bounded c in Y, Lemma 7.2 says that (b, c)/W is free from X. Hence x and (b, c) have product over X. Symmetry and projection give the free evaluation of x on every bounded test c from Y. The testing theorem identifies tp(x/Y) with the free lift of tp(x/X).

Lemma 7.6. Suppose A ≤ B are objects at eligible levels ν ≤ µ, |u, c| < ν, and the actual type

$q_{B} =$tp(u, c/B)

is the free lift of$q_{A} =$tp(u, c/A). If$q_{B}$is isolated relative to u, then$q_{A}$is isolated relative to u. Here ν is sufficiently closed for the uniform bounds at |u, c|$+ ℵ_{0}.$

Proof. By Proposition 7.3, choose a large-base isolating fragment W ⊆ B with

|W | ≤ h(|u, c|$+ ℵ_{0}) <$ν.

Let w enumerate W. The type tp(w/A) is a small-level type, computed by taking a level-ν section containing A and w. Choose a sufficiently long bounded approximation list$(w_{i})_{i<τ}$for this type inside A, where τ < ν. Enlarge its testing bound to include the arities of w and (u, c) and choose τ larger than the two exception bounds that will occur below. Put ⋃

Z = i<τ$ran(w_{i}) ⊆$A.

This is a bounded fragment.

Let$q_{A'}$have the same marginal on u as$q_{A}$and agree with it over Z. Lift$q_{A'}$freely to B. The marginal on u then agrees with the marginal of$q_{B}.$In either free coupling, symmetry identifies the joint diagram with w by the majority evaluation of tp(w/A) against the candidate tuple. Thus all but the prescribed bounded number of i < τ give the diagram of that candidate with w. Choose one index outside the two exception sets. The candidates agree on$w_{i},$because$w_{i}$lies in Z, so their free lifts agree on w. Isolation of$q_{B}$identifies the free lifts, and restriction identifies$q_{A'}$with$q_{A}.$Every approximation and comparison here has size below ν; no approximation to the whole of B is used.

## 7.3 Existence with a prescribed bound on tuple length

We first isolate the continuity requirement on the marked marginal. This will let us identify exactly where the proof for a finite mark must be supplemented for a long independent list.

Definition 7.7. A bounded marginal type p satisfies the continuity condition used here if the following holds at every sufficiently closed eligible level to which p is freely lifted. Suppose

$X_{0} ≤ X_{1} ≤ · · · ≤ X_{i} ≤ · · ·$(i < δ)

is a continuous chain at that level, its union is an object at that level, and a fixed realization b in a coupled extension satisfies

$tp(b/X_{i}) = tp(b/X_{0})_{X^{fr}_{i}}$(i < δ).

S

Thenlift of thep. same equality holds over i<δ$X_{i}.$The type at$X_{0}$is required to be the appropriate free

Every finite-tuple marginal has this property. At a limit, local character for the finite tuple gives freeness from some earlier stage, and transitivity gives freeness from$X_{0}.$This is a direct application of Proposition 6.13, including when the chain has small cofinality.

Proposition 7.8. Let λ be a sufficiently closed eligible level, let X be an object there, and let p = tp(b/X) be a finite-tuple type. For every infinite θ < λ there is a same-level extension X ≤ U containing a realization of p such that

tp(b, c/X) is isolated relative to b for every c ∈ U with |c| ≤ θ.

More generally the assertion holds for a bounded mark b satisfying Definition 7.7, with |b| ≤ θ. The closure requirements at the output level are uniform functions of bounded arities; they do not require θ to have been fixed before the level was chosen.

Proof. We prove the more general statement. Fix a bounded approximation list$I_{p}$in X which determines p at a sufficient testing arity. Choose a much larger eligible level κ and a cardinal ρ such that$λ < ρ = ρ^{λ}, ρ^{+} <$κ.

Require ρ to dominate the approximation and small-hull costs at arity λ, and choose κ after those set-sized bounds. Such choices exist: first choose a sufficiently large power$2^{ξ}$with ξ ≥ λ for ρ, and then choose an eligible κ above$ρ^{+}$and all remaining bounds. Extend X by a presentation arrow to a level-κ object$X_{0},$and choose$Y_{0} ≥ X_{0}$containing a realization b of the free lift of p.

We construct continuous pairs

$X_{i} ≤ Y_{i}$(i$≤ ρ^{+})$

at level κ, with a single fixed b in all the upper objects. The invariant on the marked marginal is

$tp(b/X_{i}) = tp(b/X_{0})_{X^{fr}_{i}}.$(5)

For$i < ρ^{+},$we also keep increasing continuous sets

$R_{i} ⊆ X_{i}, S_{i} ⊆ Y_{i}, R_{i} ⊆ S_{i}, |R_{i} |, |S_{i} | ≤$ρ,

with$I_{p} ⊆ R_{i}$and$b ⊆ S_{i}.$They are bookkeeping sets, not additional structure on the objects.

Here are the two closure requirements at a stage i with cf(i) > λ.

1. Any specified at-most-λ sets of base and top parameters from$R_{i}, S_{i}$are contained in a pair A ≤ V of level-λ subobjects of$X_{i} ≤ Y_{i},$with$A ⊆ R_{i}$and$V ⊆ S_{i}.$

2. Every tuple d of length at most λ from$S_{i}$has a sequence of at least λ copies inside$R_{i}$computing its actual type over$X_{i}$on all tests of size less than λ. For every subtuple and each such parameter test Z, all but at most |Z|$+ ℵ_{0}$of the copies give its joint D-diagram.

We explain how to arrange the requirements; in particular, they do not amount to assuming a small saturated submodel. At successor stages, process all at-most-λ lists in the current parameter sets. There are at most$ρ^{λ} = ρ$of them. Mixed Löwenheim–Skolem supplies the requested level-λ pairs. Lemma 6.9 supplies copies of each top list in the current base, at the test sizes below λ and with the displayed exception estimate. Their total number of coordinates is at most ρ. Close the sets under these operations for$λ^{+}$steps; the size is still ρ. If new elements are added later, repeat these successor closures. At a limit i of cofinality greater than λ, every requested list was contained at an earlier stage. Local character applied to that list, whose length is at most λ < cf(i), says that its actual type over$X_{i}$is free from some earlier stage. Approximations placed in a later intervening successor base still compute it over$X_{i}$by the free-extension theorem. Their copies lie in$R_{i}.$The same cofinality argument places every small-hull request in an earlier closure. This proves both requirements at the indicated limits.

At any such stage, if some list d of length at most λ from$S_{i}$makes tp(b,$d/X_{i})$nonisolated relative to b, apply Proposition 7.3. It gives a same-level extension of$X_{i}$in which this joint type has a nonfree extension while the b-marginal remains free. By type-identifying amalgamation, extend$Y_{i}$into a common$Y_{i+1},$identifying the old (b, d) with that realization. The new base is the extension just chosen. Transitivity preserves (5). At other stages use compatible extensions and the bookkeeping closures. At limits use the working scheme’s unions; Definition 7.7 preserves the marginal invariant. All these unions have size κ, since$ρ^{+} <$κ.

This process must reach an indicated stage at which every list in the second closure requirement is isolated jointly with b. Suppose not, and choose a failing list$d_{i}$at every stage with cf(i) > λ. The set of these stages is stationary in the regular cardinal$ρ^{+}.$Indeed, in any closed unbounded subset of$ρ^{+}$take a continuous increasing sequence of length$λ^{+}$and its supremum; the supremum is still below$ρ^{+},$is in the closed set, and has cofinality$λ^{+}.$

Because$S_{i}$is continuous and$|d_{i} | ≤ λ <$cf(i), there is j(i) < i with$d_{i} ⊆ S_{j(i)}.$Fodor’s pressing-down argument [Fod56] makes j(i) constant on a stationary subset. For completeness, if every fiber of a regressive map on a stationary subset of a regular cardinal were nonstationary, choose a closed unbounded set avoiding each fiber. Their diagonal intersection is closed unbounded and gives a contradiction at a point of the stationary set. The diagonal intersection is unbounded by taking an increasing countable sequence whose next point is in all the clubs indexed below the previous point; the needed intersections of fewer than the regular cardinal many clubs are closed unbounded, by interleaving their choices and taking a limit. Thus this application uses only set-indexed choices in ZFC.

There are at most$ρ^{λ} = ρ$possible lists in the resulting fixed$S_{j}.$Partitioning the stationary subset into these ρ possibilities retains a stationary piece: otherwise the intersection of$ρ < ρ^{+}$clubs avoiding the pieces is a contradiction. Consequently one fixed list d witnesses nonfree extensions at stationarily many stages. In the final union, the tuple (b, d) has length at most$λ < ρ^{+}.$Local character makes its type free from some$X_{j}.$Its restrictions at every later successor are then free from their preceding base, contradicting the chosen stationarily many nonfree extensions.

Fix a stage i at which all the required lists are isolated. We next shrink, and this step must preserve freeness for the tuples on which isolation will be transferred. Construct increasing pairs

$A_{α} ≤ U_{α}$(α$< θ^{+})$

of level-λ subobjects inside$R_{i}, S_{i}.$Keep$I_{p}$in every base and b in every top. At successor stage α + 1, take a tuple enumerating$U_{α}.$By the second closure requirement it has λ approximation copies in$R_{i}.$Include every coordinate of these copies in$A_{α+1},$and include$A_{α}, U_{α}$in the next pair, using the first closure requirement. The requests have cardinality λ. At proper limits take unions; the upper bound clause into$X_{i}, Y_{i}$keeps them strong there. Finally put

⋃ ⋃

A = α<θ+$A_{α}, U =$α<θ+$U_{α}.$

Because λ is strong limit and θ < λ, we have$θ^{+} <$λ. Both unions are level-λ objects, and the common upper bound clause gives A ≤ U.

Let c have length at most θ in U. Regularity of$θ^{+}$puts (b, c) inside some$U_{α}.$The next base contains λ copies of its type over$X_{i},$with the exception estimates above. For any fixed sufficient testing arity below λ, select a bounded subsequence longer than that arity’s exception bound. These copies are inside A and compute the actual large-base type. The majority characterization of free extension now says that

tp(b,$c/X_{i}) =$tp(b,$c/A)_{X^{fr}_{i}}.$

Explicitly, move a large-base query into A over the selected copies and over canonical approximations for the small type. Choose an index outside the exception sets for the query and its moved copy. The actual answer therefore equals the small free evaluation. The testing theorem identifies the whole type. The bounds needed for this argument are below λ, since |b, c| ≤ θ.

The large type is isolated by the choice of i. Its uniform fragment has size at most h(|b,$c|+ℵ_{0}) <$λ, so Lemma 7.6 gives isolation over A. Finally,$I_{p}$still determines the marginal on b: it did so at$X_{0},$the matrix preserved its free lift, and the same approximation answers hold on restriction to A. Bounded diagram homogeneity gives an isomorphism A ≃ X carrying these anchors to themselves. Transport of approximation evaluations carries tp(b/A) to p. Renaming U along this isomorphism gives the asserted extension of the original X.

## 7.4 All bounded lengths at one level

The preceding construction isolates tuples through one prescribed length. All-domination requires this for every bounded tuple in a single object. We obtain it by descending from a larger level with one common family of approximate retractions; the argument therefore also covers tuples that span the countable descent construction.

Theorem 7.9. At sufficiently closed eligible levels, every finite-tuple type p = tp(b/X) has an all-dominated realization: there is Y ≥ X all-dominated over X + b realizing p. More generally this holds for a bounded marginal satisfying Definition 7.7. An all-dominated realization embeds over X, b into any actual ambient containing a realization of that type, with the mixed-level conventions of Proposition 7.5.

Proof. Write ν for the desired level and fix sufficient bounded anchors$I_{p} ⊆ X$for the input marginal. Choose a much larger eligible λ > ν and lift the type to a level-λ base by a presentation arrow. Apply Proposition 7.8 at level λ with θ = ν. We obtain a pair A ≤ U of level λ such that every tuple of length at most ν in U, jointly with b, has isolation relative to b over A. The original anchors may be retained in A throughout that construction.

Choose ν distinct indices from the family in Corollary 6.16, and write the corresponding approximate retractions as$r_{j}: U −→ A$(j < ν)

such that each a ∈ A is fixed by all but finitely many of them. Use mixed Löwenheim–Skolem to choose level-ν subobjects A' ≤ U' of A ≤ U which contain$I_{p}, b$in their indicated places and satisfy

$r_{j}$[U'] ⊆ A' (j < ν). (6)

Here is the closure construction. Start with level-ν sections containing the desired entries. From the current top of size ν, adjoin to the next base all its images under the ν selected maps; there are at most ν · ν = ν coordinates. Enlarge the next top to contain that base and the old top. Iterate countably many times and take unions. Same-level chain closure and the common upper bound clause into A, U give the pair and (6).

Fix any bounded tuple d in U'. The tuple (b, d) is still bounded at ν. The maps in (6) place all its images in A'. For a test Z ⊆ A, all but at most |Z|$+ ℵ_{0}$of the maps fix Z pointwise, and hence for all those indices$D(r_{j}$(b, d), Z) = D(b, d, Z).

At a fixed testing arity below ν, choose a bounded subsequence of indices longer than the exception bound. Lemma 6.17 gives tp(b, d/A) = tp(b,$d/A')_{A^{fr}}.$

The type on the left is isolated, by the length-ν assertion at level λ. Its uniform fragment bound for the actual arity |b, d| < ν is below ν. Downward transfer gives isolation of tp(b, d/A') relative to b.

This argument applies separately to every bounded d ⊆ U'; it makes no assumption that d lies in one stage of the countable construction. Thus U' is all-dominated over A' + b. The retained anchors and bounded diagram homogeneity identify its marginal with the original p by an isomorphism A' ≃ X. Transport gives the required object over X. Its embedding into an actual ambient is Proposition 7.5.

## 7.5 Independent lists and coherent witnesses

Finite marks already have all-dominated extensions. To obtain the same conclusion for a bounded independent list of finite marks, we must first show that its finite product data determine one whole type and that this type persists along the actual coupled chains used above.

Definition 7.10. A list$(b_{i})_{i<δ}$of finite tuples is product-independent over A if each finite sublist has the product of its marginal types over A. A witnessing chain is a continuous chain$(M_{i})_{i≤δ}$of objects, with$M_{0} =$A, such that$b_{i}$lies in$M_{i+1}$and

$tp(b_{i} /M_{i}) = tp(b_{i} /A)_{M^{fr}_{i}}.$

It is an all-dominated-increment chain if, in addition,$M_{i+1}$is all-dominated over$M_{i} + b_{i}.$In uses at level µ, the chain has total size µ, in particular |δ| ≤ µ.

Lemma 7.11. Suppose$(M_{i})_{i≤δ}$is an all-dominated-increment chain over A for finite tuples$(b_{i})_{i<δ}.$If a finite tuple x in an actual coupling has product over A with every finite selection of the accumulated$b_{i},$then$tp(x/M_{δ})$is free from A.

Proof. Induct on the stage. At a successor i + 1, the finite tuple (x,$b_{i})$has product with every finite selection of earlier marks, by the finite product rules. The induction hypothesis applied to this tuple says that its joint type over$M_{i}$is free from A. Products lift freely by Proposition 6.12; hence x and$b_{i}$still have product over$M_{i}.$Proposition 7.5, applied to the all-dominated increment$M_{i+1},$makes$x/M_{i+1}$free from$M_{i}.$Transitivity makes it free from A.

At a limit j, local character for the finite tuple x gives a proper stage i < j from which$x/M_{j}$is free. The induction hypothesis and transitivity give freeness from A. All types are computed in the actual coupled ambient, so this argument asserts continuity of the specified realization, not merely existence of some independent realization at the limit.

Lemma 7.12. The following hold at sufficiently closed eligible levels.

1. Every actual product-independent list of finite tuples admits an all-dominated-increment witnessing chain, retaining its whole joint configuration in an extension of the given ambient.

2. Two lists supplied with witnessing chains have a unique whole amalgamation type over A, determined by the successive marginal types over A. This assertion also permits bounded, rather than finite, individual tuples in the witnessing chains. For a list of total length at most the level, the assertion means that one amalgam identifies the entire lists; for a bounded total list it is an equality of the bounded-list types already defined.

Proof. For the first assertion, maintain a common ambient containing the original list and the already constructed witnessing chain. At stage i, finite domination makes the actual$b_{i}$free over$M_{i}$from A: its products with finite selections of previous marks are still the original ones, since arrows preserve types. Theorem 7.9 supplies an all-dominated realization over$M_{i} + b_{i}.$Primeness embeds it into a compatible actual ambient over this tuple; alternatively, type-identifying amalgamation supplies such an ambient while retaining the original list. At limits take the coherent unions. Finite domination continues to apply, and the chain has the stipulated total size.

For uniqueness, let$M_{i^{0}}, M_{i^{1}}$be the two witnessing chains. Build common objects$N_{i}$and coherent arrows from$M_{i^{0}}, M_{i^{1}}$into$N_{i},$agreeing on A and identifying all marks already processed. At a successor, take the free lift over$N_{i}$of the next common marginal type over A, with realization c. Its restriction to either image of$M_{i^{r}}$is the prescribed type of b, by transitivity. Amalgamate ri

the next stage$M_{i+1^{0}}$with this realization over its old stage, identifying$b_{i^{0}}$with c. Then amalgamate

$M_{i+1^{1}}$in the same way, identifying its mark with the same c. The first amalgamation preserves the type of c over the other old-stage image, so the second identification is legitimate. Retain the old common object throughout. At limits, coherent unions give the required arrows. The final common ambient identifies every mark. Only bounded individual marginal types were used in a single step, which proves the stated version for bounded individual tuples as well.

Theorem 7.13. Let$b = (b_{i})_{i<δ}$be a bounded product-independent list of finite tuples over X at a sufficiently closed eligible level.

1. Its whole type is determined by the product data on finite sublists. Its free lift is product-independent and is the unique whole type with the lifted finite data.

2. The marked marginal tp(b/X) satisfies Definition 7.7.

3. There is an all-dominated object over X + b, and it embeds over these data into an actual ambient containing the given list.

Proof. Lemma 7.12 supplies witnesses for any actual list with the specified finite products and identifies their whole types. The finite projections of a free lift are the free lifts of the finite projections, by Proposition 6.12. They are therefore the required products of the lifted marginal types. Applying witnessed uniqueness at the receiving base proves the first assertion, including its mixed-level interpretation.

For continuity, take the actual coupled chain in Definition 7.7. Each finite sublist of the fixed mark is a finite tuple. Its actual free evaluations at the proper stages persist at the union by local character and transitivity. These finite data are precisely the finite data of the free lift of the original whole marginal. By the first assertion they determine its whole type at the union. This proves the second assertion without applying finite-tuple local character directly to the possibly long mark.

We may now apply the general forms of Proposition 7.8 and Theorem 7.9. To check the additional arity conditions, choose the auxiliary θ at least |b|. The parameter-set scheduling then handles (b, d) at length at most λ, and the final stationary contradiction uses length$λ < ρ^{+}.$At limits of the matrix construction, the continuity just proved preserves the fixed marked marginal. All approximation and isolation bounds are evaluated at the actual bounded joint arities. The all-length descent uses the same retractions on the concatenations (b, d), which remain bounded at the desired level. Thus all hypotheses of the two existence results hold. Primeness gives the assertion about the actual ambient.
