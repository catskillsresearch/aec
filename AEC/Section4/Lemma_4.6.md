# Lemma 4.6

Lemma 4.6 (Disjoint block transpositions). Take two set-sized families of labeled terms. In disjoint convex regions of their joint support order, suppose each region consists of two adjacent blocks, one used only by the first family and one only by the second. Interchange the blocks in every such region, retaining their internal orders and all positions outside the regions. The joint natural diagram is unchanged.

Proved in [`BlockInterchange.lean`](BlockInterchange.lean) (`BlockRegions`, binary-tree order with dividers, block repetition, orbit bound via Lemma 4.5). The older `DisjointBlockSwap` packaging is degenerate (an order automorphism cannot swap nonempty adjacent blocks); see `orderIso_swaps_blocks_empty`. Re-exported via [`Results.lean`](Results.lean).

@import "BlockInterchange.lean"
