/-
Figures/Rigidity/Rules/AvoidCollinear.lean — bump a candidate position
perpendicular to a near-collinear configuration of placed joints.

For each pair (a, b) of already-placed joints, if the candidate sits
within `tolerance` perpendicular distance from line ab, push it
outward. Only fires when noncollinearity is asserted on (candidate, a,
b) OR when the candidate is genuinely free (no asserted collinearity).
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

/-- Perpendicular distance from point `p` to the line through `a` and
`b`. -/
private def perpDist (p a b : Pos2) : Float :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  let len := (dx * dx + dy * dy).sqrt
  if len < 1e-6 then 0.0
  else ((dy * p.x - dx * p.y + b.x * a.y - b.y * a.x).abs) / len

/-- Push `p` perpendicular to line `ab` by `dist` units (sign chosen
to move away from the line). -/
private def pushPerp (p a b : Pos2) (dist : Float) : Pos2 :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  let len := (dx * dx + dy * dy).sqrt
  if len < 1e-6 then p
  else
    -- Perpendicular unit vector (rotated 90° CCW).
    let ux := -dy / len
    let uy := dx / len
    -- Sign: pick the direction that increases p's distance from the
    -- midpoint of ab (so we push outward, not inward).
    let midx := (a.x + b.x) / 2
    let midy := (a.y + b.y) / 2
    let dot := ux * (p.x - midx) + uy * (p.y - midy)
    let sign := if dot ≥ 0.0 then 1.0 else -1.0
    (p.x + sign * dist * ux, p.y + sign * dist * uy)

/-- Does the graph assert collinearity involving `id` and any pair from
`placed`? -/
private def asserted_collinear (g : ConstraintGraph) (id : Nat)
    (placed : Array (Nat × Pos2)) : Bool :=
  g.annotations.any fun ann => match ann with
  | .between a x b => (x == id) && placed.any (·.1 == a) && placed.any (·.1 == b)
  | _ => false

/-- Does the graph carry a `noncollinear (a, b, c)` with `id` ∈ {a,b,c}
and the other two among `placed`? -/
private def asserted_noncollinear (g : ConstraintGraph) (id : Nat)
    (placed : Array (Nat × Pos2)) : Bool :=
  g.annotations.any fun ann => match ann with
  | .noncollinear a b c =>
    let triple := #[a, b, c]
    triple.contains id &&
    (triple.filter (· != id)).all (fun other => placed.any (·.1 == other))
  | _ => false

@[anti_regularity 100]
def avoidCollinear : Chooser := fun ctx => do
  let g := ctx.graph
  let some cand := ctx.candidate | return none
  -- If a `between` asserts the candidate is on a segment, skip — the
  -- collinearity is intended.
  if asserted_collinear g ctx.joint ctx.placed then return none
  -- Compute the minimum perpendicular distance from `cand` to any
  -- line through two placed joints.
  let mut worst : Option (Float × Pos2 × Pos2) := none
  for (i, pi) in ctx.placed do
    for (j, pj) in ctx.placed do
      if i ≥ j then continue
      let d := perpDist cand pi pj
      match worst with
      | some (dw, _, _) => if d < dw then worst := some (d, pi, pj)
      | none            => worst := some (d, pi, pj)
  match worst with
  | none => return none
  | some (d, pi, pj) =>
    let tolerance : Float :=
      (min ctx.canvasW ctx.canvasH) * 0.05  -- 5% of the shorter canvas dim
    if d ≥ tolerance && !(asserted_noncollinear g ctx.joint ctx.placed) then
      -- Not too close to a placed line; let other rules decide.
      return none
    -- Push perpendicular until we exceed 2× tolerance, giving headroom.
    let pushDist := 2.0 * tolerance - d
    return some (pushPerp cand pi pj pushDist)

end Figures.Rigidity.Rules
