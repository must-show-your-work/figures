/-
Figures/Solver/LabelLayout.lean — post-solver label placement.

Once point positions are fixed, each `.label target text` annotation
needs a displacement offset that:
- Sits at roughly `standoff` distance from its anchor
- Doesn't overlap with other labels
- Doesn't sit on top of construction lines passing through the area

We model each label as a "ghost" particle, run a short Verlet
relaxation against three forces (tether to anchor, ghost-ghost
repulsion, segment repulsion), and read the resulting offsets back
out. This is a self-contained sub-solver — not wired into the main
`Solver.World` — because labels see the final figure as input rather
than coevolving with it.
-/

import Figures.Vec2
import Figures.Solver.Types

namespace Figures.Solver.Labels

open Figures

/-- A label ghost. `anchor` is the fixed position of the labeled shape;
`pos` is the ghost's working position (anchor + offset at convergence);
`prev` carries Verlet's implicit velocity. -/
structure Ghost where
  anchor : Pos2
  pos    : Pos2
  prev   : Pos2
deriving Inhabited

/-- A visible line segment the ghost must avoid sitting on top of.
Stored as endpoints; segment-repulsion computes point-to-segment
distance and pushes away if within cutoff. -/
structure VisibleSegment where
  a : Pos2
  b : Pos2
deriving Inhabited

/-- Label solver state. -/
structure World where
  ghosts   : Array Ghost
  segments : Array VisibleSegment
  /-- Standoff distance: tether's rest length, so each ghost equilibrates
  at roughly this distance from its anchor. -/
  standoff : Float := 28
  /-- Ghost-ghost repulsion cutoff (labels stop pushing past this). -/
  ghostCutoff : Float := 32
  /-- Segment-repulsion cutoff. -/
  segCutoff : Float := 26
  /-- Segment-repulsion strength. Comparable to tether so the two
  reach a stable balance — strong enough to push labels off segments
  they sit on, weak enough that labels don't drift far past the
  standoff radius. -/
  segStrength : Float := 1.0
deriving Inhabited

/-- Solver knobs for the label sub-solver. -/
structure Config where
  dt        : Float := 0.5
  damping   : Float := 0.75
  maxSteps  : Nat   := 200
  energyEps : Float := 1e-3
deriving Inhabited

/-- Tether force: spring from ghost toward its standoff distance.
Linear for `len ≤ 1.5·standoff` and quadratically stiffer beyond,
so labels stay near their anchor even under combined repulsion from
multiple segments and other labels. -/
private def tetherForce (standoff : Float) (g : Ghost) : Pos2 :=
  let d := Pos2.sub g.pos g.anchor
  let len := Pos2.norm d
  if len < 1e-9 then (0, 0)
  else
    let stiff : Float := 0.5
    let softCeiling := 1.5 * standoff
    let factor :=
      if len > softCeiling then 1.0 + (len - softCeiling) / standoff
      else 1.0
    Pos2.smul (-stiff * factor * (len - standoff) / len) d

/-- Ghost-ghost soft repulsion: every pair within `cutoff` pushes
apart with magnitude proportional to the overlap. -/
private def ghostPairContribution (cutoff strength : Float)
    (ghosts : Array Ghost) (i : Nat) : Pos2 :=
  let pi := ghosts[i]!.pos
  Array.range ghosts.size |>.foldl (init := ((0, 0) : Pos2)) fun acc j =>
    if i == j then acc
    else
      let pj := ghosts[j]!.pos
      let dv := Pos2.sub pi pj
      let d := Pos2.norm dv
      if d < cutoff && d > 1e-6 then
        Pos2.add acc (Pos2.smul (strength * (cutoff - d) / d) dv)
      else acc

/-- Closest point on segment `ab` to `p` (clamped to segment). -/
private def closestPointOnSegment (a b p : Pos2) : Pos2 :=
  let ab := Pos2.sub b a
  let len2 := Pos2.normSq ab
  if len2 < 1e-9 then a
  else
    let t := (Pos2.dot (Pos2.sub p a) ab) / len2
    let tClamped := min 1.0 (max 0.0 t)
    Pos2.add a (Pos2.smul tClamped ab)

/-- Unit vector perpendicular to segment ab. Used to push a ghost
that landed exactly on a segment off it in a defined direction. -/
private def perpUnit (a b : Pos2) : Pos2 :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  let len := (dx * dx + dy * dy).sqrt
  if len < 1e-9 then (0, -1)
  else (-dy / len, dx / len)

/-- Segment repulsion: for each visible segment, push the ghost away
from the closest point on the segment if within `cutoff`. When the
ghost lies exactly on the segment (d → 0), push along the segment's
perpendicular at full strength so the degenerate case doesn't silently
trap the label on the line. -/
private def segmentRepulsion (cutoff strength : Float)
    (segments : Array VisibleSegment) (p : Pos2) : Pos2 :=
  segments.foldl (init := ((0, 0) : Pos2)) fun acc s =>
    let foot := closestPointOnSegment s.a s.b p
    let dv := Pos2.sub p foot
    let d := Pos2.norm dv
    if d < cutoff then
      if d < 1e-6 then
        -- On the segment: pick perpendicular direction deterministically.
        Pos2.add acc (Pos2.smul (strength * cutoff) (perpUnit s.a s.b))
      else
        Pos2.add acc (Pos2.smul (strength * (cutoff - d) / d) dv)
    else acc

private def stepGhost (cfg : Config) (w : World) (i : Nat) (g : Ghost) : Ghost :=
  let fT := tetherForce w.standoff g
  let fG := ghostPairContribution w.ghostCutoff 1.0 w.ghosts i
  let fS := segmentRepulsion w.segCutoff w.segStrength w.segments g.pos
  let accel := Pos2.add (Pos2.add fT fG) fS
  let drift := Pos2.smul cfg.damping (Pos2.sub g.pos g.prev)
  let dt2 := cfg.dt * cfg.dt
  let newPos := Pos2.add (Pos2.add g.pos drift) (Pos2.smul dt2 accel)
  { g with prev := g.pos, pos := newPos }

private def step (cfg : Config) (w : World) : World :=
  let newGhosts := w.ghosts.mapIdx fun i g => stepGhost cfg w i g
  { w with ghosts := newGhosts }

private def kineticEnergy (w : World) : Float :=
  w.ghosts.foldl (init := 0.0) fun acc g => acc + Pos2.normSq (Pos2.sub g.pos g.prev)

/-- Run the label sub-solver until kinetic energy drops below
`energyEps` or step count hits `maxSteps`. -/
partial def solve (cfg : Config) (w₀ : World) : World :=
  let rec go (n : Nat) (w : World) : World :=
    if n ≥ cfg.maxSteps then w
    else
      let w' := step cfg w
      if kineticEnergy w' < cfg.energyEps then w'
      else go (n + 1) w'
  go 0 w₀

end Figures.Solver.Labels
