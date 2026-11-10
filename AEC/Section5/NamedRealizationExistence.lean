module

public import AEC.Section5.PackageClauses
public import AEC.Section5.WorkingScheme
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Order.InitialSeg

@[expose] public section

/-!
# Named realizations via order arrows (Proposition 5.7, existence)

Any permitted arrow out of the witness `X0` preserves the diagram of the fixed list `c`
(`diagram_preserved`; the list is bounded at the level of `X0`, hence at every higher level). Cross-level permitted arrows are supplied by
`HasPresentations.wellOrder_arrow` along well-order embeddings of the eligible cardinals.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- A well-order of cardinality `μ` (the order type of `μ.ord`). -/
abbrev cardWellOrder (μ : Cardinal.{u}) : Type u := μ.ord.ToType

theorem mk_cardWellOrder (μ : Cardinal.{u}) : #(cardWellOrder μ) = μ := by
  rw [cardWellOrder, Cardinal.mk_toType, Cardinal.card_ord]

theorem nonempty_cardWellOrder {μ : Cardinal.{u}} (hμ : μ ≠ 0) :
    Nonempty (cardWellOrder μ) :=
  Cardinal.mk_ne_zero_iff.mp (by rw [mk_cardWellOrder]; exact hμ)

/-- When `μ₀ ≤ μ`, the well-order of `μ₀` embeds as an initial segment of the well-order of
`μ`. -/
noncomputable def cardWellOrderEmbed {μ0 μ : Cardinal.{u}} (hle : μ0 ≤ μ) :
    cardWellOrder μ0 ↪o cardWellOrder μ := by
  have hord : μ0.ord ≤ μ.ord := (Cardinal.ord_le_ord).mpr hle
  have hseg : Nonempty (InitialSeg (α := cardWellOrder μ0) (β := cardWellOrder μ)
      (· < ·) (· < ·)) :=
    (Ordinal.type_le_iff (r := (· < ·)) (s := (· < ·))).mp <| by
      simpa [Ordinal.type_toType] using hord
  exact (Classical.choice hseg).toOrderEmbedding

/-- **Named realization via an order arrow.** At every eligible level `μ ≥ μ₀` there is an
object realizing the diagram of `c` as the image of a permitted arrow from `X0`. Seed objects
at each eligible level are an external hypothesis (`objectOfEmptyChain` residual). -/
theorem exists_named_realization_of_arrow (W : WorkingScheme K S)
    [hpres : HasPresentations W W.template]
    (hObj : ∀ μ hμ, Nonempty (W.Object μ hμ))
    {μ0 μ : Cardinal.{u}} (hμ0 : μ0 ∈ W.eligible) (hμ : μ ∈ W.eligible)
    (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (hι : #ι < μ0) (hle : μ0 ≤ μ) :
    ∃ Y : W.Object μ hμ,
      ∃ arr : SystemArrow K S (W.asSystem hμ0 X0) (W.asSystem hμ Y),
        W.permitted (X := X0) (Y := Y) arr ∧
        W.DiagramEq (X := X0) (Y := Y) c
          (fun i => ⟨(c i).1, arr.onVertex (c i).1 (c i).2⟩) := by
  classical
  have hμ0ne : μ0 ≠ 0 := (bot_le (a := #ι)).trans_lt hι |>.ne'
  have hμne : μ ≠ 0 := fun h => hμ0ne (le_zero_iff.mp (hle.trans_eq h))
  let I := cardWellOrder μ0
  let J := cardWellOrder μ
  let _ : Nonempty I := nonempty_cardWellOrder hμ0ne
  let _ : Nonempty J := nonempty_cardWellOrder hμne
  let emb : I ↪o J := cardWellOrderEmbed hle
  let Y : W.Object μ hμ := Classical.choice (hObj μ hμ)
  obtain ⟨arr, harr⟩ :=
    hpres.wellOrder_arrow hμ0 hμ I J X0 Y emb (mk_cardWellOrder μ0) (mk_cardWellOrder μ)
  exact ⟨Y, arr, harr, W.diagram_preserved X0 Y arr harr c hι (hι.trans_le hle)⟩

end
end AEC
