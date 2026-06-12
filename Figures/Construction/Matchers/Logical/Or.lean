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

-- Take ONLY the left branch of a disjunction. Classifying both
-- over-constrains the figure when the branches describe mutually
-- exclusive configurations (e.g. `P on ray A B ∨ P on ray A C` forces
-- P to coincide with A). The right long-term answer is multi-diagram
-- rendering — one figure per branch (task #109). For now show the
-- first branch's geometry.
@[proof_state_matcher 5]
def matchOr : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Or, #[l, _r]) =>
    let ls := (← classify l).getD #[]
    if ls.isEmpty then return none
    return some ls
  | _ => return none

end Figures.Construction.Matchers.Logical
