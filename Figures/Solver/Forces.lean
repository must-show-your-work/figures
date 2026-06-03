/-
Figures/Solver/Forces.lean — soft constraint forces.

Forces are accumulated per-particle each step (Jacobi style): the
integrator sums every registered force's contribution and applies it
as acceleration. Use forces for soft preferences (orientation,
repulsion, bounds); use projections for hard constraints (exact
incidence, segment interior).

Each constructor returns a `Force` (= `Array Particle → Array Pos2`).
A force returning `(0, 0)` for a particle has no effect that step.
-/

import Figures.Vec2
import Figures.Solver.Types

namespace Figures.Solver.Forces

open Figures

/-- Pair repulsion: every pair (i, j) within `cutoff` pushes apart
with magnitude `strength · (cutoff − d) / d` along their separation
vector. Soft Coulomb: linear in the gap to avoid singular blowup at
short range. Use to keep clustered points separated without
overdriving springs. -/
def pairRepulsion (strength cutoff : Float) : Force := fun particles =>
  let n := particles.size
  Array.range n |>.map fun i =>
    let pi := particles[i]!.pos
    Array.range n |>.foldl (init := ((0, 0) : Pos2)) fun acc j =>
      if i == j then acc
      else
        let pj := particles[j]!.pos
        let dv := Pos2.sub pi pj
        let d := Pos2.norm dv
        if d < cutoff && d > 1e-6 then
          Pos2.add acc (Pos2.smul (strength * (cutoff - d) / d) dv)
        else acc

/-- Horizon force on the axis pair `(a, b)`: pulls their y-coordinates
toward each other so the segment AB lands horizontal. Equal-and-
opposite, so the centroid y doesn't drift. Total network effect
rotates the figure around its centroid until AB is horizontal,
emergent through the spring network. -/
def horizonHorizontal (a b : ParticleId) (strength : Float) : Force := fun particles =>
  let n := particles.size
  let result : Array Pos2 := Array.replicate n (0, 0)
  if a < n && b < n then
    let ya := particles[a]!.pos.y
    let yb := particles[b]!.pos.y
    let δ := strength * (yb - ya)
    let result := result.set! a (0, δ)
    let result := result.set! b (0, -δ)
    result
  else result

/-- Apex-up: every non-axis particle below the axis line (in SVG
coords, y > y_axis) feels an upward force (negative y direction)
proportional to how far below it sits. Soft preference, not a hard
flip — the rest of the spring network may resist; the dominant
equilibrium prevails. -/
def apexUp (axisA axisB : ParticleId) (strength : Float) : Force := fun particles =>
  let n := particles.size
  if axisA < n && axisB < n then
    let yAxis := (particles[axisA]!.pos.y + particles[axisB]!.pos.y) / 2
    Array.range n |>.map fun i =>
      if i == axisA || i == axisB then ((0, 0) : Pos2)
      else
        let p := particles[i]!
        if p.pos.y > yAxis then ((0, -strength * (p.pos.y - yAxis)) : Pos2)
        else ((0, 0) : Pos2)
  else Array.replicate n (0, 0)

/-- Bounds cage: linear restoring force toward the rectangle
[cx − halfW, cx + halfW] × [cy − halfH, cy + halfH]. Inactive for
particles inside the cage; outside, pushes back toward the boundary
with magnitude `strength · overhang`. Prevents the figure from
drifting off-canvas under repulsion. -/
def boundsCage (cx cy halfW halfH strength : Float) : Force := fun particles =>
  particles.map fun p =>
    let dx :=
      if p.pos.x < cx - halfW then strength * ((cx - halfW) - p.pos.x)
      else if p.pos.x > cx + halfW then strength * ((cx + halfW) - p.pos.x)
      else 0
    let dy :=
      if p.pos.y < cy - halfH then strength * ((cy - halfH) - p.pos.y)
      else if p.pos.y > cy + halfH then strength * ((cy + halfH) - p.pos.y)
      else 0
    ((dx, dy) : Pos2)

/-- Line repulsion: every particle within `cutoff` of the infinite
line through `lineA` and `lineB` (perpendicular distance) is pushed
along the line's perpendicular, away from the line. `skip` names
particle ids that are exempt (e.g. user-named incidence anchors that
genuinely belong on the line). Magnitude is `strength · (cutoff − d) / d`
matching the standard soft-repulsion form. -/
def lineRepulsion (lineA lineB : ParticleId) (cutoff strength : Float)
    (skip : List ParticleId) : Force := fun particles =>
  let n := particles.size
  let zero : Pos2 := (0, 0)
  if lineA < n && lineB < n then
    let pa := particles[lineA]!.pos
    let pb := particles[lineB]!.pos
    let abx := pb.x - pa.x
    let aby := pb.y - pa.y
    let abLen := (abx * abx + aby * aby).sqrt
    if abLen < 1e-6 then Array.replicate n zero
    else
      let perpX := -aby / abLen
      let perpY := abx / abLen
      Array.range n |>.map fun i =>
        if skip.contains i then zero
        else if i == lineA || i == lineB then zero
        else
          let p := particles[i]!.pos
          let signed := (p.x - pa.x) * perpX + (p.y - pa.y) * perpY
          let absD := signed.abs
          if absD < cutoff && absD > 1e-6 then
            let mag := strength * (cutoff - absD) / absD
            let s := if signed ≥ 0 then 1.0 else -1.0
            ((mag * s * perpX, mag * s * perpY) : Pos2)
          else if absD ≤ 1e-6 then
            -- Right on the line: pick the (-perp) direction as a
            -- deterministic tiebreak (corresponds to "up" in SVG
            -- coordinates for a horizontal line).
            ((-strength * cutoff * perpX, -strength * cutoff * perpY) : Pos2)
          else zero
  else Array.replicate n zero

/-- Noncollinear: keeps the triangle `(a, b, c)` away from a
degenerate (zero-area) configuration. Active only when the absolute
signed area drops below `threshold`; otherwise zero. Pushes each
vertex perpendicular to its opposite edge in the direction that
increases |signed area|. Equal-and-opposite distribution across the
three vertices so the centroid doesn't drift. -/
def noncollinear (a b c : ParticleId) (strength threshold : Float) : Force :=
  fun particles =>
    let n := particles.size
    let zero : Pos2 := (0, 0)
    if a < n && b < n && c < n then
      let pa := particles[a]!.pos
      let pb := particles[b]!.pos
      let pc := particles[c]!.pos
      let signedArea :=
        (pb.x - pa.x) * (pc.y - pa.y) - (pb.y - pa.y) * (pc.x - pa.x)
      let absArea := signedArea.abs
      if absArea > threshold then Array.replicate n zero
      else
        let s := if signedArea ≥ 0 then 1.0 else -1.0
        -- Perpendicular to edge (e1, e2) rotated by 90° CCW, scaled
        -- by `strength / max(absArea, 1)` so the force ramps as the
        -- triangle approaches degeneracy.
        let factor := strength / (absArea + 1.0)
        let perpUnit (e1 e2 : Pos2) : Pos2 :=
          let dx := e2.x - e1.x
          let dy := e2.y - e1.y
          let len := (dx * dx + dy * dy).sqrt
          if len < 1e-6 then (0, 0)
          else (s * factor * (-dy) / len, s * factor * dx / len)
        -- A's opposite edge is BC; B's is CA; C's is AB. Sign s makes
        -- each push expand the (signed) area.
        let fa := perpUnit pb pc
        let fb := perpUnit pc pa
        let fc := perpUnit pa pb
        Id.run do
          let mut arr := Array.replicate n zero
          arr := arr.set! a fa
          arr := arr.set! b fb
          arr := arr.set! c fc
          return arr
    else Array.replicate n zero

end Figures.Solver.Forces
