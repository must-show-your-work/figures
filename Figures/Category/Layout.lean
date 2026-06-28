/-
Figures/Category/Layout.lean — layout pass for category-theory diagrams.

A layout takes a `Diagram` (position-free graph + cells) and returns
positions for every node. The layout registry is open: new shapes are
added by registering a `Layout` value via `@[diagram_layout]` (V2).

V1 ships with `square`, `triangle`, and a `sugiyama` generic fallback.
The auto-classifier picks the most specific template that matches the
diagram's shape; consumers can override with `Diagram.layout := some "square"`.
-/

import Figures.Category.IR
import Std.Data.HashMap

namespace Figures.Category.Layout

open Figures
open Figures.Category

/-- The result of a layout pass: a position per node. The keys are
node names (matching `Node.name`). -/
abbrev Positions := Std.HashMap String Pos2


/-! ## Canvas defaults used by every V1 layout template

User-coordinate units; the SVG canvas will be sized to fit. -/

structure CanvasParams where
  /-- Outer padding (margin) around the diagram bounding box. -/
  padding   : Float := 100
  /-- Horizontal spacing between adjacent grid cells. -/
  cellW     : Float := 220
  /-- Vertical spacing between adjacent grid cells. -/
  cellH     : Float := 130
deriving Repr, Inhabited


/-! ## Square layout

Four nodes arranged in a 2×2 grid. The four nodes are placed in source
order: nodes[0] → top-left, nodes[1] → top-right, nodes[2] → bottom-left,
nodes[3] → bottom-right.

The naturality square is the canonical case:

  F(A) -------- F(f) --------> F(B)        nodes[0]       nodes[1]
   |                            |
   α_A                         α_B
   |                            |
   v                            v
  G(A) -------- G(f) --------> G(B)        nodes[2]       nodes[3]
-/

def square (d : Diagram) (c : CanvasParams := {}) : Except String Positions := do
  unless d.nodes.size == 4 do
    throw s!"square layout: expected 4 nodes, got {d.nodes.size}"
  let p := c.padding
  let w := c.cellW
  let h := c.cellH
  let mut out : Std.HashMap String Pos2 := {}
  out := out.insert d.nodes[0]!.name (p,         p)
  out := out.insert d.nodes[1]!.name (p + w,     p)
  out := out.insert d.nodes[2]!.name (p,         p + h)
  out := out.insert d.nodes[3]!.name (p + w,     p + h)
  return out

/-- Final canvas bounds for the square layout (so the renderer can
size the viewport tightly around the diagram). -/
def squareBounds (c : CanvasParams := {}) : Pos2 :=
  (c.padding * 2 + c.cellW, c.padding * 2 + c.cellH)


/-! ## Triangle layout

Three nodes arranged as an equilateral triangle (apex at top).
Source order: nodes[0] → apex, nodes[1] → bottom-left, nodes[2] → bottom-right. -/

def triangle (d : Diagram) (c : CanvasParams := {}) : Except String Positions := do
  unless d.nodes.size == 3 do
    throw s!"triangle layout: expected 3 nodes, got {d.nodes.size}"
  let p := c.padding
  let w := c.cellW
  let h := c.cellH
  let cx := p + w / 2
  let mut out : Std.HashMap String Pos2 := {}
  out := out.insert d.nodes[0]!.name (cx,    p)
  out := out.insert d.nodes[1]!.name (p,     p + h)
  out := out.insert d.nodes[2]!.name (p + w, p + h)
  return out

def triangleBounds (c : CanvasParams := {}) : Pos2 :=
  (c.padding * 2 + c.cellW, c.padding * 2 + c.cellH)


/-! ## Layout dispatch

For V1 the dispatch is hard-coded: if `Diagram.layout` is set, use
that template; otherwise pick by node count. V2 will introduce an
open `@[diagram_layout]` registry and a classifier that inspects the
graph shape. -/

inductive Selected
  | square
  | triangle
deriving Repr, Inhabited

def selectLayout (d : Diagram) : Except String Selected :=
  match d.layout with
  | some "square"   => return .square
  | some "triangle" => return .triangle
  | some other      => throw s!"layout: unknown template '{other}'"
  | none =>
    match d.nodes.size with
    | 4 => return .square
    | 3 => return .triangle
    | n => throw s!"layout: no template registered for {n}-node diagrams (V1 supports 3 and 4); add an explicit `layout` directive"

/-- Apply the chosen layout to the diagram, returning positions and
the canvas bounds. -/
def apply (d : Diagram) (c : CanvasParams := {}) : Except String (Positions × Pos2) := do
  let sel ← selectLayout d
  match sel with
  | .square   => return (← square d c,   squareBounds c)
  | .triangle => return (← triangle d c, triangleBounds c)

end Figures.Category.Layout
