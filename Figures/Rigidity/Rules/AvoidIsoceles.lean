/-
Figures/Rigidity/Rules/AvoidIsoceles.lean — perturb a candidate that
would make any triangle with two placed joints isoceles (any two of
the three sides equal, not just all three).

Stricter than AvoidEquilateral: catches the "B=C distance from apex"
case where the apex sits on the perpendicular bisector of the base.
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

private def dist2 (a b : Pos2) : Float :=
  ((b.x - a.x) ^ 2.0 + (b.y - a.y) ^ 2.0).sqrt

@[anti_regularity 90]
def avoidIsoceles : Chooser := fun ctx => do
  let some cand := ctx.candidate | return none
  -- Same skip condition as AvoidEquilateral: don't perturb a candidate
  -- whose position is constrained by line incidence.
  let onLine := ctx.graph.annotations.any fun ann => match ann with
    | .onLineFvar p _ => p == ctx.joint
    | _ => false
  if onLine then return none
  for (_, pi) in ctx.placed do
    for (_, pj) in ctx.placed do
      let d12 := dist2 pi pj
      if d12 < 1e-6 then continue
      let d13 := dist2 cand pi
      let d23 := dist2 cand pj
      let tol := d12 * 0.05
      -- d13 ≈ d23 means cand is on the perpendicular bisector → isoceles.
      if (d13 - d23).abs < tol then
        -- Slide cand 15% toward pi to break symmetry.
        return some
          (cand.x + (pi.x - cand.x) * 0.15, cand.y + (pi.y - cand.y) * 0.15)
  return none

end Figures.Rigidity.Rules
