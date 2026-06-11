/-
Figures/Rigidity/Rules/AvoidMidpoint.lean — push a candidate off the
midpoint of any pair of placed joints.

If the candidate is at the geometric midpoint of two placed joints
(within tolerance), the renderer would suggest "midpoint" as a fact —
but the proof state doesn't assert that. Push the candidate toward
1/3 of the segment so the visual reading is clearly NOT "midpoint."
Joe's "1/3 not 1/2" rule.
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

@[anti_regularity 100]
def avoidMidpoint : Chooser := fun ctx => do
  let some cand := ctx.candidate | return none
  -- For each pair of placed joints, check if `cand` is near the midpoint.
  for (i, pi) in ctx.placed do
    for (j, pj) in ctx.placed do
      if i ≥ j then continue
      let midx := (pi.x + pj.x) / 2.0
      let midy := (pi.y + pj.y) / 2.0
      let dx := cand.x - midx
      let dy := cand.y - midy
      let distToMid := (dx * dx + dy * dy).sqrt
      let segLen := ((pj.x - pi.x) ^ 2.0 + (pj.y - pi.y) ^ 2.0).sqrt
      let tolerance := segLen * 0.1  -- 10% of segment length
      if distToMid < tolerance then
        -- Move candidate to the 1/3 point of (pi, pj) instead of midpoint.
        let third : Pos2 :=
          (pi.x + (pj.x - pi.x) / 3.0,
           pi.y + (pj.y - pi.y) / 3.0)
        return some third
  return none

end Figures.Rigidity.Rules
