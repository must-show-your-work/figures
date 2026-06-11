/-
Figures/Rigidity/Rules/OnCollinearLine.lean — place a candidate joint
on the line through two already-placed joints when they're all part
of the same collinear annotation.

Lifts the collinearity assertion (which the constraint graph merges
across overlapping triples) into actual visual collinearity:
distributes the candidate along the line, at a fraction that depends
on its index among the unplaced members.

Priority 130 — above plain AvoidCollinear (which would push the
candidate OFF a line) but below explicit Equal placement (200) and
Between placement (150). When a Between rule wants a specific
fraction, it wins; this rule fills in other collinear points that
don't have a specific position rule.
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

/-- Find a collinear annotation containing the joint, paired with
already-placed members. -/
private def findCollinearGroup (ctx : DoFContext) :
    Option (Array Nat × Array (Nat × Pos2)) := Id.run do
  for ann in ctx.graph.annotations do
    match ann with
    | .collinear ids =>
      if !ids.contains ctx.joint then continue
      let placedHere : Array (Nat × Pos2) := ids.filterMap fun id =>
        ctx.placed.findSome? fun (i, p) => if i == id then some (i, p) else none
      if placedHere.size ≥ 2 then
        return some (ids, placedHere)
    | _ => pure ()
  return none

@[anti_regularity 130]
def onCollinearLine : Chooser := fun ctx => do
  let some (allIds, placed) := findCollinearGroup ctx | return none
  let (_, p0) := placed[0]!
  let (_, p1) := placed[1]!
  -- Determine the candidate's position by its order among unplaced
  -- members. Use a fraction that lands it beyond the placed segment so
  -- the figure shows a clearly-collinear configuration.
  let unplaced : Array Nat := allIds.filter fun id =>
    !placed.any (·.1 == id)
  let idx := unplaced.findIdx? (· == ctx.joint) |>.getD 0
  -- Spread unplaced points at fractions 1.3, 1.6, 1.9, … of the segment
  -- so they cluster on the line beyond p1, distinct from one another.
  let t : Float := 1.3 + 0.3 * idx.toFloat
  return some (p0.x + (p1.x - p0.x) * t, p0.y + (p1.y - p0.y) * t)

end Figures.Rigidity.Rules
