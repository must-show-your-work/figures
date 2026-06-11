/-
Figures/Construction/Matchers/Logical/Pi.lean — telescope through Pi
binders, classify each binder's type + the conclusion.

Handles two cases:

1. **Non-dependent Pi (`P → Q`)**: classify both `P` and `Q`. Captures
   "the configuration described by the conclusion when we assume the
   antecedent." Stable across `intro` / `constructor` — the binder
   itself goes into LCtx but the conclusion stays here.

2. **Dependent Pi (`∀ x : T, body`)**: open the binder via
   `forallTelescope`, classify the binder's type + the (now-open)
   body. This is what gives us figure stability across
   `obtain ⟨…⟩ := premise` destructurings — the premise's CONSTRAINT
   STRUCTURE (e.g. `Angle V X Z`) is still in the theorem's Pi prefix
   even after the LCtx binding for it disappears.
-/

import Figures.Construction.ProofState

namespace Figures.Construction.Matchers.Logical

open Lean Meta
open Figures.Construction.DSL Figures.Construction.ProofState

@[proof_state_matcher 5]
def matchPi : Matcher := fun e => do
  let e ← instantiateMVars e
  if !e.isForall then return none
  -- Non-dependent Pi: classify both halves directly without
  -- telescoping (faster, and we get to use the literal Expr nodes).
  if !e.bindingBody!.hasLooseBVars then
    let ds := (← classify e.bindingDomain!).getD #[]
    let bs := (← classify e.bindingBody!).getD #[]
    return some (ds ++ bs)
  -- Dependent Pi: open all binders, classify each binder type + the
  -- conclusion. `forallTelescope` preserves user names on the fresh
  -- fvars, so the classifier sees `A`, `B`, `C`, `D`, … as Points
  -- with their original names.
  forallTelescope e fun binders conclusion => do
    let mut acc : Array Stmt := #[]
    for b in binders do
      let bTy ← instantiateMVars (← inferType b)
      acc := acc ++ (← classify bTy).getD #[]
    acc := acc ++ (← classify conclusion).getD #[]
    return some acc

end Figures.Construction.Matchers.Logical
