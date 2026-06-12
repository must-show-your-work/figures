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

/-- Build a topological order for joint placement: a joint's position-
determining dependencies must come before it. A `between a x b`
annotation marks `x` as depending on `a` and `b`; `onLineThrough p a
b` / `onSegment / onRay` marks `p` as depending on `a` and `b`. Within
each topological level, joints are ordered alphabetically by name. -/
private def topologicalOrder (g : ConstraintGraph) : Array Nat := Id.run do
  let n := g.joints.size
  -- Build deps: deps[i] = ids that must be placed before i.
  let mut deps : Array (Array Nat) := Array.replicate n #[]
  for ann in g.annotations do
    match ann with
    | .between a x b =>
      deps := deps.set! x ((deps[x]!).push a |>.push b)
    | .onLineThrough p a b | .onSegment p a b | .onRay p a b =>
      deps := deps.set! p ((deps[p]!).push a |>.push b)
    | _ => pure ()
  -- Iterative topological pass: place every joint whose deps are all
  -- already placed, then repeat. Alphabetical tiebreak.
  let alphabetic : Array Nat :=
    (Array.range n).qsort fun i j => g.joints[i]!.name < g.joints[j]!.name
  let mut placed : Array Nat := #[]
  let mut remaining : Array Nat := alphabetic
  while !remaining.isEmpty do
    let ready : Array Nat := remaining.filter fun id =>
      (deps[id]!).all (fun d => placed.contains d)
    if ready.isEmpty then
      -- Cycle or unresolvable deps — fall back: append whatever's left
      -- in alphabetical order.
      placed := placed ++ remaining
      remaining := #[]
    else
      placed := placed ++ ready
      remaining := remaining.filter fun id => !ready.contains id
  return placed

/-- Run synthesis: return a list of (joint id, position) for every
joint in the graph (synthetic helpers included). -/
def run (g : ConstraintGraph) (decomp : RigidityDecomposition)
    (canvasW canvasH : Float := 1280) : Lean.MetaM (Array (Nat × Pos2)) := do
  -- Topological order so between's endpoints / onLine's anchors are
  -- placed before joints that depend on them.
  let order : Array Nat := topologicalOrder g
  let mut placed : Array (Nat × Pos2) := #[]
  let mut nonsyntheticCount : Nat := 0
  for jid in order do
    if g.joints[jid]!.synthetic then continue
    let candidate := canonicalPos nonsyntheticCount g.joints.size canvasW canvasH
    nonsyntheticCount := nonsyntheticCount + 1
    let ctx : DoFContext :=
      { graph := g, placed, joint := jid,
        candidate := some candidate, canvasW, canvasH }
    let chosen ← Figures.Rigidity.AntiRegularity.chooseFor ctx
    placed := placed.push (jid, chosen.getD candidate)
  -- Refinement pass: re-apply rules with the FULL placed set so rules
  -- like `betweenPlacement` (which need both endpoints already placed)
  -- can now refine joints that originally landed at canonical fallbacks
  -- because their endpoint dependencies were placed later.
  for _ in [0:2] do
    for jid in order do
      if g.joints[jid]!.synthetic then continue
      let currentPos := placed.findSome? fun (i, p) =>
        if i == jid then some p else none
      let candidate := currentPos.getD (canvasW / 2, canvasH / 2)
      -- placedExcept omits this joint so a rule sees "everyone else"
      -- and can recompute this joint's position.
      let placedExcept := placed.filter (·.1 != jid)
      let ctx : DoFContext :=
        { graph := g, placed := placedExcept, joint := jid,
          candidate := some candidate, canvasW, canvasH }
      let chosen ← Figures.Rigidity.AntiRegularity.chooseFor ctx
      match chosen with
      | some newPos =>
        placed := placed.map fun (i, p) =>
          if i == jid then (i, newPos) else (i, p)
      | none => pure ()
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
  -- Honor `focus` annotations: rotate the figure so the focused
  -- line/segment/ray runs horizontal (positive x direction). Point
  -- focus (centering on a single joint) is a separate concern and
  -- conflicts with fitToCanvas's bbox-center translation — skip it
  -- here. Synthetic line-anchor joints have ≥ 2 incident edges to
  -- their endpoints; pick the first two and use as the orientation
  -- reference. Multiple focus annotations: first wins.
  let focusJoint? := g.annotations.findSome? fun ann => match ann with
    | .focus id => some id
    | _ => none
  let some focusJoint := focusJoint? | return placed
  if !g.joints[focusJoint]!.synthetic then return placed
  let endpoints : Array Nat := g.edges.filterMap fun e =>
    if e.a == focusJoint then some e.b
    else if e.b == focusJoint then some e.a
    else none
  if endpoints.size < 2 then return placed
  let a := endpoints[0]!
  let b := endpoints[1]!
  let posA? := placed.findSome? fun (i, p) => if i == a then some p else none
  let posB? := placed.findSome? fun (i, p) => if i == b then some p else none
  let some posA := posA? | return placed
  let some posB := posB? | return placed
  let dx := posB.x - posA.x
  let dy := posB.y - posA.y
  let len := Float.sqrt (dx * dx + dy * dy)
  if len < 1e-9 then return placed
  let cosT := dx / len
  let sinT := dy / len
  let mx := (posA.x + posB.x) / 2.0
  let my := (posA.y + posB.y) / 2.0
  return placed.map fun (id, p) =>
    let rx := p.x - mx
    let ry := p.y - my
    let newX := mx + cosT * rx + sinT * ry
    let newY := my + (-sinT) * rx + cosT * ry
    (id, (newX, newY))

end Figures.Rigidity.Synthesize
