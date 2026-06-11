/-
Figures/Rigidity/Rules/Equal.lean — place a joint at the same position
as another joint when they're asserted equal.

When the proof state contains an `A = B` hypothesis between Point
fvars, the classifier emits `assert equal A B`, the constraint graph
records it as an `.equal` annotation, and this rule picks up the
already-placed joint's position for the candidate.

Priority 200 — above all other placement rules. If the proof state
says A = B, that overrides every layout heuristic.
-/

import Figures.Rigidity.AntiRegularity

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

@[anti_regularity 200]
def equalToPlaced : Chooser := fun ctx => do
  for ann in ctx.graph.annotations do
    match ann with
    | .equal a b =>
      if a == ctx.joint then
        if let some pos := ctx.posOf b then
          return some pos
      else if b == ctx.joint then
        if let some pos := ctx.posOf a then
          return some pos
    | _ => pure ()
  return none

end Figures.Rigidity.Rules
