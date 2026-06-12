/-
Figures/Rigidity/Rules/OffLineApex.lean — place a free joint connected
to a collinear-group member at a moderate perpendicular offset.

The canonical position pool sends a "free" joint to the topmost vertex
of the regular polygon (90°). For figures whose primary feature is a
horizontal collinear stretch (e.g. Prop 3.3.i: A, B, C, D + an
off-line E with ray E→C), that puts E at the canvas top, blowing the
bbox vertical extent up to ~400px and forcing fitToCanvas to shrink
the ABCD line to ~45% of canvas width. The collinear stretch — the
*subject* of the figure — ends up clustered.

This rule fires when:
  - the candidate joint is NOT in any collinear group;
  - the candidate has a graph edge to some joint that IS in a
    collinear group;
  - that group has ≥ 2 placed members.

It places the candidate perpendicular to the group's line at a
distance of 40% of the line's extent, biased above (negative y in
canvas coords). The result: bbox aspect ratio approaches canvas's
1.78:1, fitToCanvas no longer scaleY-limited, the collinear stretch
spreads across most of the canvas width.

Priority 120: above AvoidCollinear (100) — once we've placed at a
moderate offset, the figure isn't near-collinear so the avoid rule
shouldn't override. Below CollinearOrder (160) and Between (150) —
those handle group-member placements first.
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

private def collinearGroupsContaining (g : ConstraintGraph) (id : Nat) :
    Array (Array Nat) :=
  g.annotations.filterMap fun ann => match ann with
    | .collinear ids => if ids.contains id then some ids else none
    | _ => none

private def allCollinearGroups (g : ConstraintGraph) : Array (Array Nat) :=
  g.annotations.filterMap fun ann => match ann with
    | .collinear ids => some ids
    | _ => none

/-- Find (anchorId, group) where anchorId is a joint sharing an edge
with `id` and anchorId belongs to `group`. -/
private def connectedGroupMember (g : ConstraintGraph) (id : Nat)
    (groups : Array (Array Nat)) : Option (Nat × Array Nat) :=
  g.edges.findSome? fun e =>
    let other? : Option Nat :=
      if e.a == id then some e.b
      else if e.b == id then some e.a
      else none
    match other? with
    | none => none
    | some other =>
      groups.findSome? fun grp => if grp.contains other then some (other, grp) else none

@[anti_regularity 120]
def offLineApex : Chooser := fun ctx => do
  let id := ctx.joint
  -- Skip if this joint is itself in a collinear group.
  if !(collinearGroupsContaining ctx.graph id).isEmpty then return none
  let groups := allCollinearGroups ctx.graph
  if groups.isEmpty then return none
  let some (_, groupIds) := connectedGroupMember ctx.graph id groups
    | return none
  -- Collect placed positions for the group members, to determine line
  -- direction and midpoint. Need ≥ 2 to define a line.
  let groupPlaced : Array Pos2 := groupIds.filterMap fun jid =>
    ctx.placed.findSome? fun (i, p) => if i == jid then some p else none
  if groupPlaced.size < 2 then return none
  -- Find the two extreme group members by max pairwise distance —
  -- relying on `groupIds[0]` / `groupIds[size-1]` is wrong because
  -- merge order != position order, so the "endpoints" can be
  -- arbitrary interior points (e.g. for 3.3.i's merged collinear,
  -- groupIds is [B, C, D, A] but the visual extremes are A and D).
  let mut maxDist : Float := 0.0
  let mut p0 : Pos2 := groupPlaced[0]!
  let mut pN : Pos2 := groupPlaced[0]!
  for i in [0:groupPlaced.size] do
    for j in [i+1:groupPlaced.size] do
      let pi := groupPlaced[i]!
      let pj := groupPlaced[j]!
      let d := Float.sqrt ((pj.x - pi.x) * (pj.x - pi.x) + (pj.y - pi.y) * (pj.y - pi.y))
      if d > maxDist then
        maxDist := d
        p0 := pi
        pN := pj
  let dx := pN.x - p0.x
  let dy := pN.y - p0.y
  let len := Float.sqrt (dx * dx + dy * dy)
  if len < 1e-9 then return none
  -- Perpendicular unit vector (rotate 90° CCW).
  let perpX := -dy / len
  let perpY := dx / len
  -- Bias above the line: canvas y grows downward, so prefer perpY < 0.
  let sign := if perpY < 0.0 then 1.0 else -1.0
  let offset := len * 0.4
  -- Anchor the offset at the line MIDPOINT, not the connected joint —
  -- otherwise the candidate stacks directly above whatever group member
  -- happened to be its edge-neighbor, throwing visual balance off.
  let midX := (p0.x + pN.x) / 2.0
  let midY := (p0.y + pN.y) / 2.0
  return some (midX + sign * perpX * offset, midY + sign * perpY * offset)

end Figures.Rigidity.Rules
