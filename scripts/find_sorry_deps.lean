/-
List the declarations that directly use `sorryAx` among the transitive dependencies of a
constant. Usage (from the repo root, after `lake build`):

  lake env lean scripts/find_sorry_deps.lean

Edit the `#findsorry` lines at the bottom to the constants you want to audit.
-/
import AEC
open Lean Elab Command

partial def findSorry (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack := [root]
  let mut hits : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let consts := ci.getUsedConstantsAsSet
      if consts.contains ``sorryAx then hits := hits.push n
      for c in consts do
        if !visited.contains c then stack := c :: stack
  logInfo m!"{root}: direct sorry users {hits}"

elab "#findsorry " n:ident : command => findSorry n.getId

#findsorry AEC.infra_73_tied_of_isolated
#findsorry AEC.infra_72_over_B_isolation
#findsorry AEC.lemma_7_2_tied
