# Corollary 6.16

- [Approximate retraction](ApproximateRetraction.md)

**Done** for `SingleModelData` ([`ApproxRetractionProof.lean`](ApproxRetractionProof.lean), wired in [`Results.lean`](Results.lean)). At a level of `infra_615_closed`, a same-level strong inclusion `A ≤ B` has a family of arrows `B → A` indexed by the nonzero points of `lvlOrder μ`, a set of cardinality `μ`. `A` is presented on

`W = lvlOrder μ ×ₗ (ℕ ×ₗ lvlOrder μ)`.

Block `0` is a sentinel, so every index has blocks on both sides. For block `i`, `L` is the blocks below `i` and `R` the blocks above `i`. The order isomorphism `φᵢ : MTop L R μ ≃o W` sends the fresh middle strip onto block `i`, and `φᵢ ∘ baseInto` is the inclusion of the complement. `infra_615_middle_exhaust` embeds `B` into `E(MTop)` over that complement; postcomposing with `E.map φᵢ` and `exists_present_equiv : E(W) ≃ A` lands in `A`. A point of `A` is moved only when its finite `termSupport` meets the block. The one-sided enlargement `infra_615_terminal` is not used. Lemma 6.17 is done. **Next tip:** Lemma 7.2.

**[Results.lean](Results.lean)**

@import "Results.lean"
