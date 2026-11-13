# Proposition 6.12

- [Product of types](ProductType.md)

**Done** for same-level `SingleModelData` (`BoundedProducts.lean`, thin wrap in [`Results.lean`](Results.lean)). At a recursion-closed level `μ` with `σ⁺ ≤ μ`, bounded types `p` and `q` over a level-`μ` base have a product: realize `p` by itself and freely lift `q` along `p.incl` (`stationary_free_extension_exists`). Two such products along one realization of `p` are the same Galois type when the free lifts of `q` are anchored to one approximation code (`infra_612_freeLift_unique`, `infra_612_anchored_join`, `infra_612_product_unique`): on every query up to the code's arity, both type joints are majority values on one parameter list.

**Deferred:** symmetry (`Equiv.sumComm`), `IsFiniteProduct`, base change `(p ⊗ q)^B = p_B ⊗ q^B`, mixed eligible levels, and stationarity for an untied `IsFreeLift`. The weak majority witness need not be the type joint (`same_head` stays demoted), so a bare `IsProduct` does not by itself fix the cross-diagram.

**Next:** [`proposition_6_13`](Proposition_6.13.md) is done. Proposition 6.15 and later stay blocked.

**[Results.lean](Results.lean)**

@import "Results.lean"
