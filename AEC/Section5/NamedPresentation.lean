module

public import AEC.Section5.NamedPackageTransfer
public import AEC.Section5.FixedSupportTerms

@[expose] public section

/-!
# Proposition 5.7: the named scheme with the fixed-support template

The proof of Prop 5.7 regards the presentations `F (J + H)` with the names on `J` as a template
in `H`. `WorkingScheme.withTemplate` replaces the template of a scheme; the clauses of
`IsWorkingPackageCore` do not mention the template, so they transfer unchanged.
-/

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- The same scheme with another term template. -/
def WorkingScheme.withTemplate (W : WorkingScheme K S) (F : TermTemplate K S) :
    WorkingScheme K S :=
  { W with template := F }

theorem WorkingScheme.isWorkingPackageCore_withTemplate (W : WorkingScheme K S)
    (F : TermTemplate K S) (h : IsWorkingPackageCore W) :
    IsWorkingPackageCore (W.withTemplate F) :=
  ⟨⟨h.1.union⟩, ⟨h.2.1.downward⟩, ⟨h.2.2.1.saturated⟩, ⟨h.2.2.2.exhaustion⟩⟩

end
end AEC
