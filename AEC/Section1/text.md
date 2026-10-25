# 1 Introduction


Categoricity asks whether cardinality determines a model up to isomorphism. For abstract elementary classes, the eventual categoricity conjecture predicts that uniqueness in one sufficiently large cardinal forces uniqueness in every cardinal above a uniform threshold. We prove this prediction in ZFC, with the threshold depending only on a bound for the Löwenheim–Skolem number.

## 1.1 The statement

We specify the axioms, including the union clause used throughout the proof. All structures have sets as their universes, and all languages are set-sized and finitary. We write |M | for the universe of a structure and ∥M ∥ for its cardinality.

Definition 1.1 (Abstract elementary class). An abstract elementary class (AEC) is a pair K = (C,$≤_{K}),$where C is a class of structures in a fixed language τ and$≤_{K}$is a partial order satisfying the following conditions.

(1) The class is closed under isomorphism. If$M ≤_{K}$N, then M is a τ-substructure of N. If f: N ≃ N' and$M ≤_{K}$N, then f [M]$≤_{K}$N'.

(2) Coherence: if$M_{0}$is a τ-substructure of$M_{1},$and$M_{0} ≤_{K} M_{2}$and$M_{1} ≤_{K} M_{2},$then$M_{0} ≤_{K} M_{1}.$

(3) For every nonzero ordinal δ and increasing chain$(M_{i}: i <$δ) under$≤_{K},$its union U belongs to C and$M_{i} ≤_{K} U$for all i < δ. If also$M_{i} ≤_{K} N$for every i, then$U ≤_{K}$N.

(4) There is an infinite cardinal ℓ ≥ |τ$| + ℵ_{0}$such that, for every M ∈ C and A ⊆ |M |, there is$N ≤_{K} M$with A ⊆ |N | and ∥N ∥ ≤ |A| + ℓ.

The least possible ℓ is denoted LS(K). A strong map is an isomorphism onto a strong substructure of its codomain. The class is categorical in κ if it has a model of cardinality κ and all its models of that cardinality are isomorphic.

The chain axioms equivalently give unions and the common-upper-bound clause for nonempty set-indexed directed systems of strong inclusions. We also use the corresponding direct limits of coherent strong maps, obtained by renaming their injective images. No intersection axiom is included.

Theorem 1.2 (Uniform eventual categoricity). For every infinite cardinal λ there is a cardinal µ(λ) ≥ λ such that the following holds for every AEC K with LS(K) ≤ λ:

∃κ ≥ µ(λ) K is categorical in κ =⇒ ∀κ' ≥ µ(λ) K is categorical in κ'.

The same threshold is used in the premise and the conclusion.

In particular, Theorem 1.2 resolves Shelah’s eventual categoricity conjecture positively. No amalgamation, joint embedding, tameness, no-maximal-models, or arbitrarily-large-models hypothesis is assumed. The starting categoricity cardinal may be a successor, a regular limit, or a singular cardinal. The theorem asserts the existence of a threshold, without prescribing a numerical bound for it.

On the resulting categorical tail, every model strongly embeds into every model of at least its cardinality. Indeed, the Löwenheim–Skolem axiom supplies a strong submodel of the smaller cardinality, and categoricity identifies it with the given model. Taking a larger target gives proper strong extensions and a common target for any two models. Thus the tail has joint embedding and no maximal models.

It is useful to separate the uniform quantifier from the main structural argument.

Theorem 1.3 (The qualitative form). An AEC categorical in unboundedly many cardinals is categorical on a tail of the cardinals.

Here “unbounded” means unbounded in the class of all cardinals, and a tail contains every cardinal above some fixed cardinal. The set-coding argument in Proposition 2.3 proves the equivalence of the two theorems. Once that reduction is made, arbitrarily large models are available. The order construction in Theorem 2.6 then supplies actual models at every sufficiently large cardinal; subsequent categoricity arguments concern both existence and uniqueness.

The uniform theorem applies in particular to sentences of$L_{ω_{1}},ω$in countable languages, where countable conjunctions and disjunctions are allowed but quantifier strings are finite. For such a sentence φ, choose a countable fragment containing it and order its models by elementarity for that fragment. This is an AEC with Löwenheim–Skolem number$ℵ_{0}$[BV17, Example 2.0.2]. The models and their isomorphisms are unchanged, so the same$µ(ℵ_{0})$works for all these sentences. The prescribed$ℶ_{ω_{1}}$threshold in the classical infinitary formulation remains a separate question [BV15, Conjecture 1.1].

## 1.2 History and scope

Morley’s categoricity theorem gives the countable first-order prototype: a countable theory categorical in one uncountable cardinal is categorical in every uncountable cardinal [Mor65]. Its structural approach connects uniqueness of models with stability and dimension. The geometry of strongly minimal sets, developed by Baldwin and Lachlan [BL71, Sections 1–2], provides a central antecedent for classification by bases. In an AEC, elementary compactness and the first-order description of types are not part of the axioms. The corresponding amalgamation, independence, and geometry therefore require separate constructions.

Shelah’s eventual categoricity conjecture asks for an eventual dichotomy between categoricity and noncategoricity; see [She09, Conjecture N.4.2] and [BV15]. The equivalent formulation using one threshold depending on an LS bound is discussed in [Vas17a, Remark 1.3]. Our set-coding argument makes that reduction explicit: it treats bounded categoricity spectra as well as classes categorical at unboundedly many cardinals. An explicit numerical threshold is a further question, separate from the existential threshold in Theorem 1.2; compare [She09, Conjecture N.4.3(1)(b)]. Under CH, the companion [Ope26, Theorem 1.1] constructs an AEC K with LS(K)$= ℵ_{0}$that is categorical on a higher tail but not at$ℶ_{(2^{ℵ_{0}}} + = ℶ_{ω_{2}},$ruling out this prescribed endpoint for )

arbitrary AECs.

Substantial special cases have been established. Makkai and Shelah proved transfer from sufficiently large successor categoricity for$L_{κ,ω}$-theories when κ is strongly compact [MS90, Conclusion 5.1]. Grossberg and VanDieren obtained upward categoricity transfer from one sufficiently large successor cardinal for tame AECs with amalgamation, joint embedding, and arbitrarily large models [GV06, Theorem 5.2]. Boney subsequently derived tameness from strongly compact cardinals and, combining it with the Grossberg–VanDieren transfer, established eventual categoricity for arbitrary AECs with a successor starting cardinal under a proper class of strongly compact cardinals [Bon14]. These results explain the importance of removing restrictions on the starting cardinal as well as structural hypotheses on the class.

Universal classes admit a ZFC transfer without assuming amalgamation [Vas17b, Theorem 7.3]. Tameness, amalgamation, and primes give another transfer [Vas18, Theorem 3.8]. Shelah and Vasey prove a ZFC categoricity theorem for excellent AECs and obtain broader results using strongly compact cardinals, or the weak generalized continuum hypothesis (WGCH), that is,$2^{κ} < 2^{κ^{+}}$for every infinite cardinal κ, together with amalgamation [SV24, Theorem 14.2 and Corollaries 14.7, 14.10]. Under WGCH, amalgamation, and arbitrarily large models, Vasey also gives a classification of categoricity spectra [Vas19, Corollary 9.7]. These hypotheses supply substantial structure. Here the amalgamation, bounded-tuple calculus, and geometry needed for the working schemes are constructed at selected levels from the AEC axioms and unbounded categoricity.

The proof uses several established methods in forms that are proved locally. Order presentations originate in the work of Ehrenfeucht and Mostowski [EM56]; their AEC formulation and functorial maps are developed in [She09, IV.0.8–IV.0.9 and IV.0.12]. We retain a finite-support presentation throughout the proof. Its extraction uses classical partition-calculus methods [ER56], while the later isolation argument uses Fodor’s pressing-down method [Fod56]. Stationary independence and local character are central to Shelah’s good frames [She09, II.2.1]. Sections 6 and 7 establish the bounded-tuple calculus, relative isolation, and dominated extensions required for the systems used here.

A version-sensitive issue matters for the order argument. Boney and Vasey [BV15, Fact 1.4 and the discussion of Claim 1.5, pp. 3–4] identify a gap in the unrestricted syntactic-characterization claim of Shelah’s Chapter IV and withdraw an earlier attempted repair. Their valid variants with exponentiation or cofinality assumptions do not cover all the starting cardinals of Theorem 1.2. We prove the required reversal of strong maps directly in Theorem 3.11.

Finite systems and dimension-raising arguments have a long history in nonelementary categoricity. Shelah’s existence and uniqueness methods [She83, Sections 3–5] are antecedents of the passage from one additional dimension to a larger cardinal. The modern treatment in [SV24, Definition 8.16 and Lemma 11.6] distinguishes amalgamated completion from strong uniqueness onto a prescribed target. Both properties are needed below and are proved separately. Our final cardinal induction uses exact boundary maps for systems whose basis pieces may have different cardinalities.

Espíndola has announced eventual categoricity for arbitrary AECs and further accessible-category results [Esp22], and subsequently an explicit-threshold categoricity theorem [Esp23, Theorem 4.1]. These are separate public claims. The argument here constructs its working-scheme calculus, isolation, marked and geometric boundary lifting, and common-level closure directly. None of these interfaces is imported from those preprints.

## 1.3 Proof overview

By the set-coding reduction in Section 2, it suffices to fix one AEC K categorical in unboundedly many cardinals and prove categoricity on a tail. The proof first builds structure at selected cardinals, called working levels, and only at the end transfers it to every larger cardinal. A tuple is bounded at a level µ when its length is strictly less than µ.

From orders to comparison of tuples. An order presentation E assigns a model to a linear order: each element is represented by a label and finitely many indices, and an order embedding induces a strong map by substituting indices. Section 3 uses specially chosen orders to control the automorphism orbits of short tuples. A small subpresentation can be aligned with a larger presentation so that all its short tuples have matching orbit records. An elimination chain then proves that a strong map can be reversed on any prescribed short tuple. The small model supplies the alignment; the larger model accommodates the enumeration of the small model’s tuples. This avoids an exponentiation hypothesis at the categoricity cardinal.

In Section 4, the resulting equivalence classes of tuples under strong maps stabilize as the categoricity cardinal increases. These are the comparison diagrams used later. Finite supports give two further tools: a bound on the parameter sets needed to distinguish comparisons, and simultaneous placement of coherent bounded prescriptions. Together they yield amalgamation and homogeneity for bounded tuples at suitable countably cofinal closure levels.

A calculus that can be applied to systems. The same tools will be needed for finite systems of models, not only for individual models. Section 5 records their precise hypotheses as a working scheme: a finite system shape, specified arrows, one finite-support presentation, and compatible tuple comparisons. Sections 6 and 7 derive the calculus from this package. A type over a base is determined by identification of tuples in an amalgam over that base. Its distinguished free extensions are computed by long approximation sequences already in the base. The isolation construction gives extensions controlled by a specified mark: the full type of each additional bounded tuple, together with the mark, is determined by the mark’s type and a bounded fragment of the base. Such extensions have the primeness and uniqueness needed for iteration.

Marked systems detect growth of a geometry. Section 8 shows that adjoining a finite mark and an extension controlled in this way again gives a working scheme. Iterating produces a model at each subset of a finite axis set, with commuting strong maps. Its boundary consists of the proper-subset vertices and their maps. Section 9 first completes a compatible boundary map into a common extension, then extends a boundary isomorphism onto the prescribed target. The return-tree argument keeps full maps coherent along individual branches but retains only boundary maps in the common accumulator. This distinction lets the orbit bound control joint comparisons across different faces, including their actual equalities.

Section 10 chooses a minimal singleton type, one with a unique nonalgebraic extension over each relevant base. Its realizations form the points of a pregeometry, with independence defined by finite products of the type. We retain a distinguished strong copy of its base model$M_{0},$with a fixed diagram for its enumeration, in the later models; these are the pointed models used below. Exact lifting for all finite marked systems at one common level rules out a proper strong extension with no new points. A downward construction then extends this no-growth conclusion to arbitrary larger cardinalities. Thus the geometry detects every proper extension, and its basis cardinality equals model cardinality above the resulting threshold.

From geometric systems to a categorical tail. Sections 11 and 12 organize bases into finitely many pieces assigned to vertices. Tiled order presentations give systems with these pieces; a paired induction establishes their working packages and classification by prescribed basis maps. A second boundary argument gives exact lifting for every finite geometric shape at suitable levels.

The two finite-dimensional applications require separate common-level choices. Section 13 supplies both: fixed set codes for all finite constructions and their bound requests produce a level where every finite depth is available. The geometric application is made after the marked application has supplied the no-growth threshold. Finally, Section 14 starts from a common geometric level and inducts on the maximum cardinality of the basis pieces, simultaneously for all finite shapes. One additional axis records the previously constructed isomorphism at each extension step; coherent unions handle limits. The zero-axis case gives pointed categoricity. The

Löwenheim–Skolem axiom and categoricity at one fixed smaller cardinal place the chosen base pattern in every sufficiently large model. Forgetting that base gives the qualitative theorem, and the set-code reduction gives the uniform theorem.

Figure 1 summarizes the proof and the two uses of common-level closure.

## 1.4 Conventions

All size variables are cardinals unless explicitly called ordinals. An assertion about bounded tuples at a level µ concerns tuples of length strictly below µ. Eligible working levels have countable cofinality and are strong limits closed under the displayed bounds. Whenever smaller adequate levels are needed cofinally below a working level, that requirement is stated and included in the closure bookkeeping. Automorphisms of an index order always mean automorphisms of its pure linear order. Charts, auxiliary hulls, and basis choices are not added to the structures whose isomorphisms are being compared.
