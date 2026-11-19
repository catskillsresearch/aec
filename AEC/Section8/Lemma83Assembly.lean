module

public import AEC.Section8.OrderColimit83
public import AEC.Section8.MarkedPairTransport
public import AEC.Section8.Lemma83Single

@[expose] public section

/-!
# Lemma 8.3 (P.scheme): assembly of the faithful conclusion from marked template values

`infra_83_conclusion_of_marked_values`: a pair template `F^b` on the doubled one-vertex shape with
values `X_I ≤ Y_I` (presentations `eX`, `eY`, edge = inclusion), mark occurrences `mk_I`, and
order embeddings acting by commuting arrows `F^b(f)` that preserve the marks (exactly the data of
`infra_83_pair_template_clauses`) gives the faithful `Lemma83Conclusion` on any tail `T` of
eligible levels on which the values (on well-orders) are marked pairs (the mark realizes the prescribed type
under some identification `realEq` of positions, and `Y_I` is all-dominated over `X_I + mk_I`). Clause (3) is
`infra_83_clause3_single`. So `infra_83_lemma_8_3_full_single` reduces to the marked-pair
property of the template values (`infra_83_bounded_arity_free`, `infra_83_all_dominated`).
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Assembly of faithful Lemma 8.3 from marked template values (proved).** -/
theorem infra_83_conclusion_of_marked_values (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (F : TermTemplate K oneVertexShape.{u}.doubled)
    (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      P.scheme.Object #I hI)
    (eX : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v,
      ((F.present I).obj (Sum.inl v)).carrier ≃[K.τ]
        ((P.scheme.asSystem hI (X I hI)).obj v).carrier)
    (eY : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v,
      ((F.present I).obj (Sum.inr v)).carrier ≃[K.τ]
        ((P.scheme.asSystem hI (Y I hI)).obj v).carrier)
    (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
        (P.scheme.asSystem hI (Y I hI)))
    (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI)))
    (hincl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v x,
      (incl I hI).onVertex v (eX I hI v x) =
        eY I hI v ((F.present I).edge
          (show (oneVertexShape.{u}).doubled.specified (Sum.inl v) (Sum.inr v) from rfl) x))
    (harr : ∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J]
      (f : I ↪o J) (hI : #I ∈ P.eligible) (hJ : #J ∈ P.eligible),
      ∃ (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hJ (X J hJ)))
        (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hI (Y I hI))
          (P.scheme.asSystem hJ (Y J hJ))),
        SystemArrow.comp (incl I hI) onY = SystemArrow.comp onX (incl J hJ) ∧
        (∀ v x, onX.onVertex v (eX I hI v x) =
          eX J hJ v ((F.onOrder f).onVertex (Sum.inl v) x)) ∧
        (∀ v x, onY.onVertex v (eY I hI v x) =
          eY J hJ v ((F.onOrder f).onVertex (Sum.inr v) x)) ∧
        ∀ i, (⟨(mk I hI i).1, onY.onVertex (mk I hI i).1 (mk I hI i).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hJ (Y J hJ))) = mk J hJ i)
    (T : Set Cardinal.{u}) (hT : Tail P.scheme.eligible T)
    (hmark : ∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
      ∃ realEq : ULift.{u} (Fin Pr.n) ≃ (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))).idx,
      SameGaloisType (asTuple (incl I (Tail.mem hT hI)) trivial
            (fun j : ULift.{u} (Fin Pr.n) => mk I (Tail.mem hT hI) j.down))
          (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))) realEq (Equiv.refl _) ∧
        AllDominated (incl I (Tail.mem hT hI)) trivial (ULift.{u} (Fin Pr.n))
          (fun j => mk I (Tail.mem hT hI) j.down)) :
    Lemma83Conclusion P.scheme Pr := by
  let val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
      #I ∈ T → MarkedPair K oneVertexShape P.scheme Pr := fun I _ _ _ hI =>
    ⟨#I, Tail.mem hT hI, X I (Tail.mem hT hI), Y I (Tail.mem hT hI), incl I (Tail.mem hT hI),
      trivial, ULift.{u} (Fin Pr.n), fun j => mk I (Tail.mem hT hI) j.down,
      (hmark I hI).choose, (hmark I hI).choose_spec.1, (hmark I hI).choose_spec.2⟩
  refine ⟨F, T, hT, val, fun I _ _ _ hI => eX I (Tail.mem hT hI),
    fun I _ _ _ hI => eY I (Tail.mem hT hI),
    fun I _ _ _ hI => ⟨rfl, fun v x => hincl I (Tail.mem hT hI) v x,
      fun _ _ h => h.elim, fun _ _ h => h.elim⟩,
    fun I J _ _ _ _ _ _ f hI hJ => ?_,
    infra_83_clause3_single P Pr T val (fun _ _ _ _ _ => rfl)⟩
  obtain ⟨onX, onY, hc, hX, hY, hm⟩ := harr I J f (Tail.mem hT hI) (Tail.mem hT hJ)
  exact ⟨⟨onX, onY, trivial, trivial, hc, Equiv.refl _, fun j => hm j.down⟩, hX, hY⟩

/-- **Assembly, prescribed-index form (proved).** As `infra_83_conclusion_of_marked_values`,
but the marks of the value at `I` are indexed by the prescribed tuple's coordinates
`(Pr.assign X_I).idx` (through `Pr.arity`), with `realEq = id` — the indexing of the
Lemma 8.2 (1) marked pairs (`infra_82_marked_pair_exists`), so the values can be compared with
them by `infra_83_marked_of_sub` without reindexing. -/
theorem infra_83_conclusion_of_marked_values_assign (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (F : TermTemplate K oneVertexShape.{u}.doubled)
    (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      P.scheme.Object #I hI)
    (eX : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v,
      ((F.present I).obj (Sum.inl v)).carrier ≃[K.τ]
        ((P.scheme.asSystem hI (X I hI)).obj v).carrier)
    (eY : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v,
      ((F.present I).obj (Sum.inr v)).carrier ≃[K.τ]
        ((P.scheme.asSystem hI (Y I hI)).obj v).carrier)
    (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
        (P.scheme.asSystem hI (Y I hI)))
    (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI)))
    (hincl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v x,
      (incl I hI).onVertex v (eX I hI v x) =
        eY I hI v ((F.present I).edge
          (show (oneVertexShape.{u}).doubled.specified (Sum.inl v) (Sum.inr v) from rfl) x))
    (harr : ∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J]
      (f : I ↪o J) (hI : #I ∈ P.eligible) (hJ : #J ∈ P.eligible),
      ∃ (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hJ (X J hJ)))
        (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hI (Y I hI))
          (P.scheme.asSystem hJ (Y J hJ))),
        SystemArrow.comp (incl I hI) onY = SystemArrow.comp onX (incl J hJ) ∧
        (∀ v x, onX.onVertex v (eX I hI v x) =
          eX J hJ v ((F.onOrder f).onVertex (Sum.inl v) x)) ∧
        (∀ v x, onY.onVertex v (eY I hI v x) =
          eY J hJ v ((F.onOrder f).onVertex (Sum.inr v) x)) ∧
        ∀ i, (⟨(mk I hI i).1, onY.onVertex (mk I hI i).1 (mk I hI i).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hJ (Y J hJ))) = mk J hJ i)
    (T : Set Cardinal.{u}) (hT : Tail P.scheme.eligible T)
    (hmark : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ T),
      SameGaloisType (asTuple (incl I (Tail.mem hT hI)) trivial
            (fun j => mk I (Tail.mem hT hI) (Pr.arity (Tail.mem hT hI) (X I (Tail.mem hT hI)) j)))
          (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))) (Equiv.refl _) (Equiv.refl _) ∧
        AllDominated (incl I (Tail.mem hT hI)) trivial
          (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))).idx
          (fun j => mk I (Tail.mem hT hI) (Pr.arity (Tail.mem hT hI) (X I (Tail.mem hT hI)) j))) :
    Lemma83Conclusion P.scheme Pr := by
  let val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
      #I ∈ T → MarkedPair K oneVertexShape P.scheme Pr := fun I _ _ _ hI =>
    ⟨#I, Tail.mem hT hI, X I (Tail.mem hT hI), Y I (Tail.mem hT hI), incl I (Tail.mem hT hI),
      trivial, (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))).idx,
      fun j => mk I (Tail.mem hT hI) (Pr.arity (Tail.mem hT hI) (X I (Tail.mem hT hI)) j),
      Equiv.refl _, (hmark I hI).1, (hmark I hI).2⟩
  refine ⟨F, T, hT, val, fun I _ _ _ hI => eX I (Tail.mem hT hI),
    fun I _ _ _ hI => eY I (Tail.mem hT hI),
    fun I _ _ _ hI => ⟨rfl, fun v x => hincl I (Tail.mem hT hI) v x,
      fun _ _ h => h.elim, fun _ _ h => h.elim⟩,
    fun I J _ _ _ _ _ _ f hI hJ => ?_,
    infra_83_clause3_single P Pr T val (fun _ _ _ _ _ => rfl)⟩
  obtain ⟨onX, onY, hc, hX, hY, hm⟩ := harr I J f (Tail.mem hT hI) (Tail.mem hT hJ)
  refine ⟨⟨onX, onY, trivial, trivial, hc,
    (Pr.arity (Tail.mem hT hI) (X I (Tail.mem hT hI))).trans
      (Pr.arity (Tail.mem hT hJ) (X J (Tail.mem hT hJ))).symm, fun j => ?_⟩, hX, hY⟩
  refine (hm _).trans ?_
  show mk J _ _ = mk J _ (Pr.arity _ _ ((Pr.arity _ _).symm _))
  rw [Equiv.apply_symm_apply]

end AEC
