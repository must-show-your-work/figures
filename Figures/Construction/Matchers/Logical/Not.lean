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
    let innerStmts := (← classify inner).getD #[]
    -- Only claim the match if we have content to wrap. Otherwise yield
    -- to even lower-priority matchers (which there aren't currently,
    -- but the contract should be honored — empty claim swallows the
    -- shape from any future low-priority fallback).
    if innerStmts.isEmpty then return none
    return some <| innerStmts.map fun s => match s with
      | .assert (.app head args) _ => .assert (.app "¬" [.app head args]) ""
      | other => other
  | _ => return none

end Figures.Construction.Matchers.Logical
