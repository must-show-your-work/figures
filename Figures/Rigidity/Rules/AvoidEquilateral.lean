/-
Figures/Rigidity/Rules/AvoidEquilateral.lean — perturb a candidate that
would form an equilateral triangle with two placed joints.

If placing the candidate at the proposed position yields a triangle
whose three side lengths are within tolerance of each other, perturb
the candidate so the triangle becomes scalene.
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

private def dist (a b : Pos2) : Float :=
  ((b.x - a.x) ^ 2.0 + (b.y - a.y) ^ 2.0).sqrt

@[anti_regularity 100]
def avoidEquilateral : Chooser := fun ctx => do
  let some cand := ctx.candidate | return none
  -- For each pair of placed joints (pi, pj), check if (cand, pi, pj)
  -- would be near-equilateral.
  for (_, pi) in ctx.placed do
    for (_, pj) in ctx.placed do
      let d12 := dist pi pj
      if d12 < 1e-6 then continue
      let d13 := dist cand pi
      let d23 := dist cand pj
      let avg := (d12 + d13 + d23) / 3.0
      let tol := avg * 0.05  -- 5% tolerance
      let dev12 := (d12 - avg).abs
      let dev13 := (d13 - avg).abs
      let dev23 := (d23 - avg).abs
      if dev12 < tol && dev13 < tol && dev23 < tol then
        -- Stretch the candidate away from the centroid of (pi, pj) so
        -- d13 ≠ d23 ≠ d12.
        let cx := (pi.x + pj.x) / 2.0
        let cy := (pi.y + pj.y) / 2.0
        let dx := cand.x - cx
        let dy := cand.y - cy
        let len := (dx * dx + dy * dy).sqrt
        if len < 1e-6 then return none
        -- Scale by 1.4 so the apex is taller than the base; produces a
        -- distinctly scalene triangle.
        return some (cx + dx * 1.4, cy + dy * 1.4)
  return none

end Figures.Rigidity.Rules
