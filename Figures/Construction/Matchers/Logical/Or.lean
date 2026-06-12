/-
Figures/Construction/Matchers/Logical/Or.lean — split disjunctions
and classify both branches.

A disjunction in a hypothesis (e.g. case analysis) or in a goal
(e.g. Pasch's "L intersects AC OR L intersects BC") describes
alternative configurations. The figure should reflect both — the
union of constraints from each branch — so the rendered figure
illustrates the geometric setting in which either alternative could
hold.
-/

import Figures.Construction.ProofState

namespace Figures.Construction.Matchers.Logical

open Lean Meta
open Figures.Construction.DSL Figures.Construction.ProofState

-- Emit CONSTRUCTS from both branches (so the figure shows the geometric
-- setting referenced by either alternative — e.g. ray A B *and* ray A C
-- when the disjunction is `P on ray A B ∨ P on ray A C`) but ASSERTS only
-- from the left branch. Classifying both branches' asserts would
-- over-constrain (forcing P onto both rays). One-figure-per-branch
-- rendering remains future work (task #109).
@[proof_state_matcher 5]
def matchOr : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Or, #[l, r]) =>
    let ls := (← classify l).getD #[]
    let rs := (← classify r).getD #[]
    if ls.isEmpty && rs.isEmpty then return none
    let rKeep := rs.filter fun s => match s with
      | .construct _ _ => true
      | .assert (.app head _) _ => head == "hidden"
      | _ => false
    return some (ls ++ rKeep)
  | _ => return none

end Figures.Construction.Matchers.Logical
