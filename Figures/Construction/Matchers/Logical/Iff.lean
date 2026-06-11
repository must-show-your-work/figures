/-
Figures/Construction/Matchers/Logical/Iff.lean — split biconditionals
into both sides. Each side describes the same configuration (the
theorem says they're equivalent), so the figure incorporates both.
-/

import Figures.Construction.ProofState

namespace Figures.Construction.Matchers.Logical

open Lean Meta
open Figures.Construction.DSL Figures.Construction.ProofState

@[proof_state_matcher 5]
def matchIff : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Iff, #[l, r]) =>
    let ls := (← classify l).getD #[]
    let rs := (← classify r).getD #[]
    return some (ls ++ rs)
  | _ => return none

end Figures.Construction.Matchers.Logical
