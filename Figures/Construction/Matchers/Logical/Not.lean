/-
Figures/Construction/Matchers/Logical/Not.lean — wrap each emitted
constraint from the inner classification with a `¬` head. Specific
Not patterns (e.g. `¬OppositeRay`) live as higher-priority matchers
and supersede this generic wrapping.
-/

import Figures.Construction.ProofState

namespace Figures.Construction.Matchers.Logical

open Lean Meta
open Figures Figures.Construction.DSL Figures.Construction.ProofState

@[proof_state_matcher 5]
def matchNot : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Not, #[inner]) =>
    let inner := (← classify inner).getD #[]
    return some <| inner.map fun s => match s with
      | .assert (.app head args) _ => .assert (.app "¬" [.app head args]) ""
      | other => other
  | _ => return none

end Figures.Construction.Matchers.Logical
