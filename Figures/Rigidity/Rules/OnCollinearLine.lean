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

/-- Parametric position of `p` projected onto the line through p0→p1.
0 = at p0, 1 = at p1, > 1 beyond p1, < 0 beyond p0. -/
private def projectT (p0 p1 p : Pos2) : Float :=
  let dx := p1.x - p0.x
  let dy := p1.y - p0.y
  let len2 := dx * dx + dy * dy
  if len2 < 1e-12 then 0.0
  else ((p.x - p0.x) * dx + (p.y - p0.y) * dy) / len2

@[anti_regularity 130]
def onCollinearLine : Chooser := fun ctx => do
  let some (allIds, placed) := findCollinearGroup ctx | return none
  let (_, p0) := placed[0]!
  let (_, p1) := placed[1]!
  -- Compute the maximum `t` of any already-placed member of this
  -- collinear group (after projecting their positions onto the p0→p1
  -- line). The candidate goes 0.3 beyond that.
  let mut maxT : Float := 1.0
  for (_, p) in placed do
    let t := projectT p0 p1 p
    if t > maxT then maxT := t
  let t := maxT + 0.3
  return some (p0.x + (p1.x - p0.x) * t, p0.y + (p1.y - p0.y) * t)

end Figures.Rigidity.Rules
