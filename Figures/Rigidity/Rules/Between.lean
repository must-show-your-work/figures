/-
Figures/Rigidity/Rules/Between.lean — when `between a x b` is asserted,
place x at 1/3 of segment ab (not 1/2 — that would suggest midpoint).
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

/-- Find a betweenness assertion `between a x b` for the candidate
joint, where both `a` and `b` are placed. -/
private def findBetween (g : ConstraintGraph) (id : Nat)
    (placed : Array (Nat × Pos2)) : Option (Pos2 × Pos2) :=
  g.annotations.findSome? fun ann => match ann with
  | .between a x b =>
    if x != id then none
    else
      let posA := placed.findSome? fun (i, p) => if i == a then some p else none
      let posB := placed.findSome? fun (i, p) => if i == b then some p else none
      match posA, posB with
      | some pa, some pb => some (pa, pb)
      | _, _ => none
  | _ => none

@[anti_regularity 150]
def betweenPlacement : Chooser := fun ctx => do
  let some (pa, pb) := findBetween ctx.graph ctx.joint ctx.placed | return none
  -- 1/3 of the segment from a to b (matches Joe's not-midpoint rule).
  return some (pa.x + (pb.x - pa.x) / 3.0, pa.y + (pb.y - pa.y) / 3.0)

end Figures.Rigidity.Rules
