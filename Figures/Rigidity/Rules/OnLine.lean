/-
Figures/Rigidity/Rules/OnLine.lean — when `onLineThrough p a b` (or
`onSegment` / `onRay`) is asserted, snap p to the appropriate position
along line ab. Default fraction is 0.4 (so it's not at midpoint and
not at the endpoints). For `onSegment` it's interior; for `onRay` it
can extend beyond b.
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

@[anti_regularity 140]
def onLinePlacement : Chooser := fun ctx => do
  for ann in ctx.graph.annotations do
    match ann with
    | .onLineThrough p a b
    | .onSegment p a b =>
      if p != ctx.joint then continue
      let posA := ctx.placed.findSome? fun (i, pp) => if i == a then some pp else none
      let posB := ctx.placed.findSome? fun (i, pp) => if i == b then some pp else none
      match posA, posB with
      | some pa, some pb =>
        -- 40% along the segment (not midpoint, not endpoint).
        return some (pa.x + (pb.x - pa.x) * 0.4, pa.y + (pb.y - pa.y) * 0.4)
      | _, _ => pure ()
    | .onRay p a b =>
      if p != ctx.joint then continue
      let posA := ctx.placed.findSome? fun (i, pp) => if i == a then some pp else none
      let posB := ctx.placed.findSome? fun (i, pp) => if i == b then some pp else none
      match posA, posB with
      | some pa, some pb =>
        -- 1.3× along the ray (past b but not too far).
        return some (pa.x + (pb.x - pa.x) * 1.3, pa.y + (pb.y - pa.y) * 1.3)
      | _, _ => pure ()
    | _ => pure ()
  return none

end Figures.Rigidity.Rules
