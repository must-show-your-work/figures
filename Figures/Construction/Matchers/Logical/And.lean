/-
Figures/Construction/Matchers/Logical/And.lean — split conjunctions
into their conjuncts and classify each independently.

Logical decomposition, not a geometric property — the And node carries
no figure information itself, but its children might.
-/

import Figures.Construction.ProofState

namespace Figures.Construction.Matchers.Logical

open Lean Meta
open Figures.Construction.DSL Figures.Construction.ProofState

@[proof_state_matcher 5]
def matchAnd : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``And, #[l, r]) =>
    let ls := (← classify l).getD #[]
    let rs := (← classify r).getD #[]
    return some (ls ++ rs)
  | _ => return none

end Figures.Construction.Matchers.Logical
