/-
Figures/Solver/Projections.lean — hard-constraint projections.

Each projection is applied after the Verlet step in Gauss-Seidel
order (each sees the latest post-correction state). Pinned particles
are never moved; otherwise the named particle's position is replaced
by the closest point satisfying the constraint.

Conventions:
- Projections clamp to manifolds (segment, line, circle, …) by
  computing the foot of the perpendicular and then bounding the
  projected parameter as needed.
- The whole-array signature lets a projection read other particles'
  current positions (e.g. the segment AB requires reading A and B
  before projecting X onto it).
-/

import Figures.Vec2
import Figures.Solver.Types

namespace Figures.Solver.Projections

open Figures

/-- Closest point on the infinite line through `a` and `b` to `p`.
Returns `a` if `a = b`. -/
private def projectOntoLine (a b p : Pos2) : Pos2 :=
  let ab := Pos2.sub b a
  let len2 := Pos2.normSq ab
  if len2 < 1e-9 then a
  else
    let t := (Pos2.dot (Pos2.sub p a) ab) / len2
    Pos2.add a (Pos2.smul t ab)

/-- Closest point on the segment from `a` to `b` to `p`. Clamps the
projection parameter to `[ε, 1-ε]` so a `between A X B` projection
keeps X strictly interior — touching an endpoint would degenerate
the configuration. -/
private def projectOntoSegmentInterior (a b p : Pos2) : Pos2 :=
  let ab := Pos2.sub b a
  let len2 := Pos2.normSq ab
  if len2 < 1e-9 then a
  else
    let t := (Pos2.dot (Pos2.sub p a) ab) / len2
    let ε : Float := 0.1
    let tClamped := min (1.0 - ε) (max ε t)
    Pos2.add a (Pos2.smul tClamped ab)

/-- Replace one particle's position by `pos`, preserving its `prev`
implicit velocity so projections don't artificially zero out
momentum. The Verlet integrator picks up `pos - prev` next step. -/
private def setPos (particles : Array Particle) (id : ParticleId) (pos : Pos2) :
    Array Particle :=
  if id < particles.size then
    particles.set! id { particles[id]! with pos := pos }
  else particles

/-- `between a x b`: snap x to the closest interior point of segment ab.
Clamps to `[0.1, 0.9]` along the segment to keep X strictly between A
and B (not coinciding with either endpoint). -/
def between (a x b : ParticleId) : Projection := fun particles =>
  if a < particles.size && b < particles.size && x < particles.size
      && !particles[x]!.pinned then
    setPos particles x
      (projectOntoSegmentInterior particles[a]!.pos particles[b]!.pos particles[x]!.pos)
  else particles

/-- `incidentOnLine p a b`: snap p onto the infinite line through a
and b. Use this when the line's geometry is defined by two anchor
particles (e.g. `line_through A B`, or two `incident P L` asserts
naming the same L). -/
def incidentOnLine (p a b : ParticleId) : Projection := fun particles =>
  if a < particles.size && b < particles.size && p < particles.size
      && !particles[p]!.pinned then
    setPos particles p
      (projectOntoLine particles[a]!.pos particles[b]!.pos particles[p]!.pos)
  else particles

/-- `collinear ids`: snap every particle in `ids` after the first two
onto the infinite line through the first two. `ids` of length < 2
is a no-op (nothing to project onto). -/
def collinear (ids : List ParticleId) : Projection :=
  match ids with
  | a :: b :: rest => fun particles =>
    if a < particles.size && b < particles.size then
      let pa := particles[a]!.pos
      let pb := particles[b]!.pos
      rest.foldl (init := particles) fun ps id =>
        if id < ps.size && !ps[id]!.pinned then
          setPos ps id (projectOntoLine pa pb ps[id]!.pos)
        else ps
    else particles
  | _ => id

/-- Intersection of two lines through `(a1, b1)` and `(a2, b2)`.
Returns the intersection point when the lines are non-parallel;
returns the four-point centroid as a deterministic fallback when
they're parallel. -/
private def lineIntersection (a1 b1 a2 b2 : Pos2) : Pos2 :=
  let d1x := b1.x - a1.x
  let d1y := b1.y - a1.y
  let d2x := b2.x - a2.x
  let d2y := b2.y - a2.y
  let det := d2x * d1y - d1x * d2y
  if det.abs < 1e-9 then
    ((a1.x + b1.x + a2.x + b2.x) / 4, (a1.y + b1.y + a2.y + b2.y) / 4)
  else
    let px := a2.x - a1.x
    let py := a2.y - a1.y
    let t1 := (d2x * py - d2y * px) / det
    (a1.x + t1 * d1x, a1.y + t1 * d1y)

/-- `intersect2 a1 b1 a2 b2 x`: snap `x` to the intersection of the
infinite lines through `(a1, b1)` and `(a2, b2)`. Use this when two
`between` asserts share a middle particle (e.g. `between A X B` and
`between C X D` both naming X) — projecting onto each segment serially
oscillates because two non-parallel segments don't generally overlap;
projecting to the line intersection satisfies both constraints in
one step. -/
def intersect2 (a1 b1 a2 b2 xi : ParticleId) : Projection := fun particles =>
  if a1 < particles.size && b1 < particles.size
      && a2 < particles.size && b2 < particles.size
      && xi < particles.size && !particles[xi]!.pinned then
    setPos particles xi
      (lineIntersection particles[a1]!.pos particles[b1]!.pos
                        particles[a2]!.pos particles[b2]!.pos)
  else particles

/-- `halfPlane a b pid signSide margin`: snap `pid` to the requested
side of the infinite line through `(a, b)`. `signSide > 0` requires
`pid` to sit on the side where `cross(ab, ap) ≥ 0`; `signSide < 0` for
the opposite. When `pid` is on the wrong side OR closer to the line
than `margin`, it's projected to the foot of the perpendicular on
the line and offset by `margin` in the required perpendicular
direction. Using "closer than margin" rather than just "wrong side"
keeps spring forces from dragging the particle progressively onto
the line each step. -/
def halfPlane (a b pid : ParticleId) (signSide margin : Float) : Projection :=
  fun particles =>
    if a < particles.size && b < particles.size && pid < particles.size
        && !particles[pid]!.pinned then
      let pa := particles[a]!.pos
      let pb := particles[b]!.pos
      let p := particles[pid]!.pos
      let abx := pb.x - pa.x
      let aby := pb.y - pa.y
      let abLen2 := abx * abx + aby * aby
      if abLen2 < 1e-9 then particles
      else
        let abLen := abLen2.sqrt
        let perpX := -aby
        let perpY := abx
        let signed := (p.x - pa.x) * perpX + (p.y - pa.y) * perpY
        let perpDist := signed / abLen  -- signed perpendicular distance
        if perpDist * signSide ≥ margin then particles
        else
          let perpUnitX := perpX / abLen
          let perpUnitY := perpY / abLen
          let t := ((p.x - pa.x) * abx + (p.y - pa.y) * aby) / abLen2
          let footX := pa.x + t * abx
          let footY := pa.y + t * aby
          let s := if signSide ≥ 0 then 1.0 else -1.0
          let newPos : Pos2 :=
            (footX + s * margin * perpUnitX, footY + s * margin * perpUnitY)
          setPos particles pid newPos
    else particles

end Figures.Solver.Projections
