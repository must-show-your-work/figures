/-
Figures/Rigidity/Synthesize.lean — algebraic position synthesis.

For each joint (visited in a deterministic order — alphabetical by
name), compute a canonical candidate position from the layout pool,
then hand the joint to the anti-regularity registry. If a rule claims
the joint with a perturbed position, use that; otherwise fall back to
the canonical candidate.

This MVP doesn't use the rigidity decomposition for the placement
algorithm itself — the canonical layout + registry-perturbation is
sufficient for the cases we care about. The pebble-game output is
recorded in the synthesizer's diagnostics for future use.

Subsequent revisions can introduce true Henneberg construction
(placing rigid components via 2-distance triangulation from already-
placed vertices); the registry API stays unchanged.
-/

import Figures.Rigidity.Types
import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Synthesize

open Figures Figures.Rigidity

/-- Canonical position for the i-th joint in the layout pool: vertices
of a regular polygon centered on the canvas, alphabetized order maps
to bottom-left, bottom-right, top, etc. -/
private def canonicalPos (i n : Nat) (canvasW canvasH : Float) : Pos2 :=
  let cx := canvasW / 2.0
  let cy := canvasH / 2.0
  let r  := (min cx cy) * 0.75
  -- Angle offsets so i=0 lands bottom-left (~210°), i=1 bottom-right
  -- (~330°), i=2 top (~90°), then evenly distributed.
  let angle : Float := match i with
    | 0 => 210.0
    | 1 => 330.0
    | 2 => 90.0
    | k => 90.0 + (k.toFloat * 360.0 / n.toFloat)
  let radians := angle * 3.14159265358979 / 180.0
  (cx + r * radians.cos, cy - r * radians.sin)

/-- Run synthesis: return a list of (joint id, position) for every
joint in the graph (synthetic helpers included). -/
def run (g : ConstraintGraph) (decomp : RigidityDecomposition)
    (canvasW canvasH : Float := 1280) : Lean.MetaM (Array (Nat × Pos2)) := do
  -- Visit joints in alphabetical order by name so the layout pool
  -- maps consistently across re-elabs.
  let order : Array Nat :=
    (Array.range g.joints.size).qsort fun i j =>
      g.joints[i]!.name < g.joints[j]!.name
  let mut placed : Array (Nat × Pos2) := #[]
  let mut nonsyntheticCount : Nat := 0
  for jid in order do
    if g.joints[jid]!.synthetic then continue
    -- Canonical fallback position based on visit order.
    let candidate := canonicalPos nonsyntheticCount g.joints.size canvasW canvasH
    nonsyntheticCount := nonsyntheticCount + 1
    let ctx : DoFContext :=
      { graph := g, placed, joint := jid,
        candidate := some candidate, canvasW, canvasH }
    let chosen ← Figures.Rigidity.AntiRegularity.chooseFor ctx
    placed := placed.push (jid, chosen.getD candidate)
  -- Synthetic joints: place at the centroid of their incident edges'
  -- placed vertices. If isolated, drop to canvas center.
  for jid in order do
    if !g.joints[jid]!.synthetic then continue
    let neighborPositions : Array Pos2 := g.edges.filterMap fun e =>
      if e.a == jid then
        placed.findSome? fun (i, p) => if i == e.b then some p else none
      else if e.b == jid then
        placed.findSome? fun (i, p) => if i == e.a then some p else none
      else none
    let p : Pos2 := if neighborPositions.isEmpty then (canvasW / 2, canvasH / 2)
      else
        let cx := neighborPositions.foldl (init := 0.0) (· + ·.x) / neighborPositions.size.toFloat
        let cy := neighborPositions.foldl (init := 0.0) (· + ·.y) / neighborPositions.size.toFloat
        (cx, cy)
    placed := placed.push (jid, p)
  -- Unused for now — record for future Henneberg-style construction.
  let _ := decomp
  return placed

end Figures.Rigidity.Synthesize
