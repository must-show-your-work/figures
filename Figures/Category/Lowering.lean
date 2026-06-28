/-
Figures/Category/Lowering.lean — lower a `Diagram` to a `Scene Pos2`.

Pipeline: select a layout template, compute node positions, then emit
`text` shapes for nodes, `arrow` shapes for edges, and `text` shapes
with `↻` glyphs for commutativity cell centroids.

The output `Scene` flows through the existing `Figures.SVG.render`
backend unchanged — that's the point of having a shared Scene IR.
-/

import Figures
import Figures.Category.IR
import Figures.Category.Layout

namespace Figures.Category.Lowering

open Figures
open Figures.Category
open Figures.Category.Layout

/-- Centroid of an array of positions. -/
private def centroid (pts : Array Pos2) : Pos2 :=
  if pts.isEmpty then (0, 0)
  else
    let sx := pts.foldl (fun s p => s + p.1) 0
    let sy := pts.foldl (fun s p => s + p.2) 0
    let n  := pts.size.toFloat
    (sx / n, sy / n)

/-- Shorten an `a → b` chord by `shortenBy` user-units at each end so
the arrow doesn't run into the node-label glyphs. The default of
`50` reserves enough breathing room for two-character labels at
22px text — adjust if you start using longer node labels. -/
private def shorten (a b : Pos2) (shortenBy : Float := 50) : Pos2 × Pos2 :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let len := (dx * dx + dy * dy).sqrt
  if len < shortenBy * 2 then (a, b)
  else
    let ux := dx / len
    let uy := dy / len
    let a' : Pos2 := (a.1 + ux * shortenBy, a.2 + uy * shortenBy)
    let b' : Pos2 := (b.1 - ux * shortenBy, b.2 - uy * shortenBy)
    (a', b')

/-- Emit a `text` shape for a node. -/
private def nodeShape (n : Node) (pos : Pos2) : Shape Pos2 :=
  -- Center the text on the position by anchoring slightly above-center.
  -- SVG `<text>` anchors at the baseline; nudge by +6px so the glyph
  -- visually centers on `pos`.
  .text n.name (pos.1, pos.2 + 6) n.label.fallbackText

/-- Emit an `arrow` shape for an edge plus an optional `text` shape
for its label. The arrow ID is `e_<src>_<tgt>`; the label ID (when
present) is `lbl_<src>_<tgt>`.

`diagCentroid` is the centroid of ALL node positions in the diagram.
Label offsets are computed perpendicular to the chord AWAY from
`diagCentroid` — that puts boundary-edge labels on the outside of
the diagram instead of crammed toward its center. -/
private def edgeShapes (e : Edge) (srcP tgtP : Pos2) (diagCentroid : Pos2) :
    Array (Shape Pos2) := Id.run do
  let (a, b) := shorten srcP tgtP
  let arrowId := s!"e_{e.source}_{e.target}"
  let arrow : Shape Pos2 := .arrow arrowId a b e.bend e.head .default
  let labelText := e.label.fallbackText
  if labelText.isEmpty then
    return #[arrow]
  let mx := (a.1 + b.1) / 2
  let my := (a.2 + b.2) / 2
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let len := (dx * dx + dy * dy).sqrt
  let offset : Float := 30  -- user units perpendicular from the chord
  let labelP : Pos2 :=
    if len < 0.001 then (mx, my)
    else
      -- Two candidate perpendicular directions: (-dy/len, dx/len)
      -- and its negation. Pick the one that points AWAY from the
      -- diagram centroid so the label lands on the outside.
      let perp1 : Pos2 := (-dy / len, dx / len)
      let toMid : Pos2 := (mx - diagCentroid.1, my - diagCentroid.2)
      let sign  : Float := if perp1.1 * toMid.1 + perp1.2 * toMid.2 > 0 then 1 else -1
      (mx + perp1.1 * offset * sign,
       my + perp1.2 * offset * sign + 6)
  let labelId := s!"lbl_{e.source}_{e.target}"
  let labelShape : Shape Pos2 := .text labelId labelP labelText
  return #[arrow, labelShape]

/-- Emit a `↻` symbol for a commutativity cell — placed at the
centroid of all node positions referenced in the cell's paths. -/
private def cellShape (idx : Nat) (positions : Positions) (cell : Cell) : Option (Shape Pos2) :=
  let allNames := cell.paths.flatMap id
  let pts : Array Pos2 := allNames.filterMap fun n => positions[n]?
  if pts.isEmpty then none
  else
    let (cx, cy) := centroid pts
    some <| .text s!"commute_{idx}" (cx, cy + 6) "↻"

/-! ## Top-level lowering -/

/-- Lower a `Diagram` to a `Scene Pos2`. Returns the scene + canvas
bounds (so callers can size the SVG viewport tightly). -/
def lower (d : Diagram) (c : Layout.CanvasParams := {}) :
    Except String (Scene Pos2 × Pos2) := do
  let (positions, bounds) ← Layout.apply d c
  -- Centroid of all node positions — used by edge-label placement
  -- to push labels to the outside of the diagram.
  let nodeCenters : Array Pos2 := d.nodes.filterMap fun n => positions[n.name]?
  let diagCentroid := centroid nodeCenters
  -- Nodes
  let nodeShapes := d.nodes.map fun n =>
    match positions[n.name]? with
    | some pos => nodeShape n pos
    | none     => nodeShape n (0, 0)  -- shouldn't happen if layout is sane
  -- Edges (with labels positioned away from centroid)
  let edgeShapes := d.edges.flatMap fun e =>
    match positions[e.source]?, positions[e.target]? with
    | some sp, some tp => Lowering.edgeShapes e sp tp diagCentroid
    | _, _             => #[]
  -- Commute markers (one ↻ per cell)
  let cellShapes := d.cells.mapIdx fun i cell => cellShape i positions cell
  let cellShapesFiltered := cellShapes.filterMap id
  let scene : Scene Pos2 := {
    shapes := nodeShapes ++ edgeShapes ++ cellShapesFiltered
  }
  return (scene, bounds)

end Figures.Category.Lowering
