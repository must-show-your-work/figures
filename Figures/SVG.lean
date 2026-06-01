/-
Geometry/Construction/SVG.lean — baseline IR → SVG renderer.

Pure-naive layout: free points get spread on a regular polygon, free
lines get staggered angles through the canvas center, free circles get
default radii at staggered offsets. Constraints (`between`, `incident`,
etc.) are read but NOT enforced — for MVP we just want pixels on the
screen and a working pipeline. A constraint-aware layout pass is a
follow-up.

Derived objects (`construct X := segment A B`, etc.) inherit positions
from their constituents.

Annotations: `label` emits SVG `<text>`, `highlight` decorates the
target's style, `angleMark` and `callout` are TODO for MVP.

Output is a full standalone SVG document with `xmlns` so any consumer
(browser, lean.nvim's libresvg rasterizer via the atlas SVG parser,
etc.) can render it without additional wrapping.
-/

import Figures
import Std.Data.HashMap

namespace Figures.SVG

open Figures


/-! ## Geometry / canvas types -/

structure Pos where
  x : Float
  y : Float
deriving Repr, Inhabited

/-- A laid-out object — what gets drawn. Lines carry two reference
points; the renderer extends them across the canvas at draw time. -/
inductive Drawn
  | point (p : Pos)
  | segment (a b : Pos)
  | line (a b : Pos)
  | circle (center : Pos) (radius : Float)
deriving Repr, Inhabited

structure Canvas where
  width : Float := 480
  height : Float := 480
  /-- Margin from the edge for layout placement (points won't be put
  closer than this to the canvas edge). -/
  margin : Float := 40
deriving Repr, Inhabited

def Canvas.center (c : Canvas) : Pos := ⟨c.width / 2, c.height / 2⟩

/-- Layout radius — how big the inscribed circle for free-point
placement is. -/
def Canvas.layoutRadius (c : Canvas) : Float :=
  (min c.width c.height) / 2 - c.margin


/-! ## Naive layout

Walk `base ++ extensions` in order. For each `.exist` step assign a
position from the appropriate naive scheme; for each `.construct`
step, dispatch on the RHS shape and inherit positions from the
referenced constituents. Asserts are ignored at this layer.
-/

private def π : Float := 3.141592653589793

/-- Polygon vertex at angle θ on the canvas's layout circle. -/
private def polygonVertex (c : Canvas) (θ : Float) : Pos :=
  let r := c.layoutRadius
  let cc := c.center
  -- SVG y grows downward; flip the y-component so the diagram reads
  -- like a math diagram (positive y up).
  ⟨cc.x + r * Float.cos θ, cc.y - r * Float.sin θ⟩

/-- A horizontal-ish line through the center at a given slope, returned
as two reference points roughly at the canvas edges. -/
private def lineThroughCenter (c : Canvas) (θ : Float) : Pos × Pos :=
  let cc := c.center
  let r := c.layoutRadius * 1.3  -- a little past the polygon so the line "exits" visibly
  let dx := r * Float.cos θ
  let dy := r * Float.sin θ
  (⟨cc.x - dx, cc.y + dy⟩, ⟨cc.x + dx, cc.y - dy⟩)


/-- Layout state: per-kind counters drive the position-picking sequence,
plus the actual map from name to drawn geometry. -/
private structure LayoutState where
  pointCount : Nat := 0
  lineCount : Nat := 0
  circleCount : Nat := 0
  layout : Std.HashMap String Drawn := {}
  deriving Inhabited

/-- Allocate the next polygon vertex position. `totalPoints` is the
expected count (so we can space evenly even though we discover names
one at a time). -/
private def takeNextPointPos (canvas : Canvas) (st : LayoutState) (totalPoints : Nat) : Pos :=
  let n := max totalPoints 1
  let θ := π / 2 - 2 * π * st.pointCount.toFloat / n.toFloat  -- start at top, go clockwise
  polygonVertex canvas θ

/-- Allocate the next line position. We stagger them at angles that
don't coincide with the polygon vertices. -/
private def takeNextLine (canvas : Canvas) (st : LayoutState) : Pos × Pos :=
  -- Different starting offset than the points, plus a per-line shift.
  let θ := π / 6 + π / 4 * st.lineCount.toFloat
  lineThroughCenter canvas θ

/-- Count the number of free-point `.exist` steps across base + extensions,
used to space them evenly. -/
private def countFreePoints (steps : List Step) : Nat :=
  steps.foldl
    (fun n step => match step with
      | .exist _ .point => n + 1
      | _               => n)
    0

/-- Evaluate an `Expr` as a (drawn) geometry referencing earlier names.
Best-effort: unrecognised shapes return `none`. Used by `construct`
dispatch. -/
private def evalExpr (layout : Std.HashMap String Drawn) (e : Expr) : Option Drawn :=
  match e with
  | .name n => layout[n]?
  | .num _ => none
  | .app "segment" [.name a, .name b] => do
      let .point pa ← layout[a]? | none
      let .point pb ← layout[b]? | none
      some (.segment pa pb)
  | .app "line" [.name a, .name b] => do
      let .point pa ← layout[a]? | none
      let .point pb ← layout[b]? | none
      some (.line pa pb)
  | .app "midpoint" [.name a, .name b] => do
      let .point pa ← layout[a]? | none
      let .point pb ← layout[b]? | none
      some (.point ⟨(pa.x + pb.x) / 2, (pa.y + pb.y) / 2⟩)
  | _ => none

/-- One layout step: handle `exist` (allocate a fresh position by kind),
`construct` (compute position from RHS), `assert` (no-op for MVP). -/
private def stepLayout (canvas : Canvas) (totalPoints : Nat) (st : LayoutState) (s : Step) :
    LayoutState :=
  match s with
  | .exist name .point =>
    let pos := takeNextPointPos canvas st totalPoints
    { st with
      pointCount := st.pointCount + 1
      layout := st.layout.insert name (.point pos) }
  | .exist name .line =>
    let (a, b) := takeNextLine canvas st
    { st with
      lineCount := st.lineCount + 1
      layout := st.layout.insert name (.line a b) }
  | .exist name .circle =>
    let r := canvas.layoutRadius / 2
    -- Stagger circle centers along the diagonal.
    let cc := canvas.center
    let shift := (st.circleCount.toFloat - 1) * 20
    let center : Pos := ⟨cc.x + shift, cc.y + shift⟩
    { st with
      circleCount := st.circleCount + 1
      layout := st.layout.insert name (.circle center r) }
  | .exist _ _ => st  -- other kinds (segment-as-free, ray, angle, scalar, other) — skip for MVP
  | .construct name rhs =>
    match evalExpr st.layout rhs with
    | some d => { st with layout := st.layout.insert name d }
    | none   => st  -- unrecognised RHS — silently skip; downstream sees a hole
  | .assert _ => st  -- constraints are ignored by the naive layout

/-- Walk all steps (base + extensions) and produce the final layout map. -/
def buildLayout (c : Construction) (canvas : Canvas := {}) : Std.HashMap String Drawn :=
  let allSteps := c.base ++ c.extensions
  let total := countFreePoints allSteps
  let final := allSteps.foldl (stepLayout canvas total) ({} : LayoutState)
  final.layout


/-! ## Rendering -/

/-- The position to anchor an annotation to. For points, that's the
point itself; for segments/lines, the midpoint of the reference
endpoints; for circles, the center. -/
private def anchorOf (d : Drawn) : Pos :=
  match d with
  | .point p          => p
  | .segment a b      => ⟨(a.x + b.x) / 2, (a.y + b.y) / 2⟩
  | .line a b         => ⟨(a.x + b.x) / 2, (a.y + b.y) / 2⟩
  | .circle center _  => center

/-- Per-attribute selectors driven by an optional `Style`. Computing
each attribute once (rather than appending a `style` snippet to a
defaulted element) avoids duplicate-attribute XML which libresvg
rejects with `resvg_parse_tree_from_data failed: 6`. -/
private def strokeColorAttr (style : Option Style) (default : String) : String :=
  match style with
  | some (.color c) => s!" stroke=\"{c}\""
  | _               => s!" stroke=\"{default}\""

private def strokeWidthAttr (style : Option Style) (default : String) : String :=
  match style with
  | some .bold => " stroke-width=\"3\""
  | _          => s!" stroke-width=\"{default}\""

private def dashAttr (style : Option Style) : String :=
  match style with
  | some .dashed => " stroke-dasharray=\"5,3\""
  | some .dotted => " stroke-dasharray=\"1,2\""
  | _            => ""

private def opacityAttr (style : Option Style) : String :=
  match style with
  | some .faint => " stroke-opacity=\"0.35\""
  | _           => ""

/-- Combined stroke-related attributes for line/segment/circle outlines.
Each attribute appears at most once in the output. -/
private def lineStyleAttrs (style : Option Style) : String :=
  strokeColorAttr style "black"
    ++ strokeWidthAttr style "1.5"
    ++ dashAttr style
    ++ opacityAttr style

/-- Collect a per-name style override from annotations. Last one wins
on a given name. -/
private def collectStyles (anns : List Annotation) : Std.HashMap String Style :=
  anns.foldl
    (fun m a => match a with
      | .highlight target style => m.insert target style
      | _                       => m)
    ({} : Std.HashMap String Style)

-- Format a Float for SVG: trim trailing zeros and a dangling decimal
-- point. `Float.toString` emits 6 decimal places by default
-- (`240.000000`), which clutters the output. Uses the deprecated
-- `dropRightWhile`/`dropRight` to keep `String`-typed values; the
-- successor APIs return `String.Slice`, which complicates the loop.
set_option linter.deprecated false in
private def fmt (x : Float) : String :=
  let s := toString x
  if s.contains '.' then
    let trimmed := s.dropRightWhile (· == '0')
    if trimmed.endsWith "." then trimmed.dropRight 1 else trimmed
  else s

/-- Emit the SVG element for one named drawn object. -/
private def drawnSvg (name : String) (d : Drawn) (style : Option Style) : String :=
  let lineAttrs := lineStyleAttrs style
  match d with
  | .point p =>
    -- Points: a filled disc, no stroke. `.bold` highlight enlarges the
    -- radius rather than thickening a stroke that doesn't exist.
    let r := match style with | some .bold => "6" | _ => "4"
    s!"  <circle id=\"{name}\" cx=\"{fmt p.x}\" cy=\"{fmt p.y}\" r=\"{r}\" fill=\"black\" />"
  | .segment a b =>
    s!"  <line id=\"{name}\" x1=\"{fmt a.x}\" y1=\"{fmt a.y}\" x2=\"{fmt b.x}\" y2=\"{fmt b.y}\"{lineAttrs} />"
  | .line a b =>
    s!"  <line id=\"{name}\" x1=\"{fmt a.x}\" y1=\"{fmt a.y}\" x2=\"{fmt b.x}\" y2=\"{fmt b.y}\"{lineAttrs} />"
  | .circle c r =>
    s!"  <circle id=\"{name}\" cx=\"{fmt c.x}\" cy=\"{fmt c.y}\" r=\"{fmt r}\" fill=\"none\"{lineAttrs} />"

/-- Emit the SVG element for one annotation. -/
private def annotationSvg (layout : Std.HashMap String Drawn) (a : Annotation) : Option String :=
  match a with
  | .label target text => do
      let d ← layout[target]?
      let p := anchorOf d
      -- Nudge label up-right of the anchor so it doesn't overlap.
      some s!"  <text x=\"{fmt (p.x + 8)}\" y=\"{fmt (p.y - 8)}\" font-family=\"serif\" font-size=\"14\" font-style=\"italic\">{text}</text>"
  | .highlight _ _ =>
      -- Handled by `collectStyles` / `drawnSvg`; no separate SVG element.
      none
  | .angleMark _ _ _ _ =>
      -- TODO: arc at the angle. Skipping for MVP.
      none
  | .callout target text => do
      let d ← layout[target]?
      let p := anchorOf d
      -- Crude callout: a small text + horizontal pointer line.
      some <| String.intercalate "\n"
        [ s!"  <line x1=\"{fmt (p.x + 12)}\" y1=\"{fmt p.y}\" x2=\"{fmt (p.x + 60)}\" y2=\"{fmt p.y}\" stroke=\"#555\" stroke-width=\"0.75\" />"
        , s!"  <text x=\"{fmt (p.x + 65)}\" y=\"{fmt (p.y + 4)}\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#555\">{text}</text>" ]


/-- Render a construction as a standalone SVG document. Standalone so
the same output works in a browser, a `ProofWidgets.Html`-via-SvgParser
pipeline (lean.nvim), or `IO.println` debug. -/
def render (c : Construction) (canvas : Canvas := {}) : String :=
  let layout := buildLayout c canvas
  let styles := collectStyles c.annotations
  let lines := layout.toList.map fun (name, d) =>
    drawnSvg name d (styles[name]?)
  let annLines := c.annotations.filterMap (annotationSvg layout)
  let header :=
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{fmt canvas.width}\" height=\"{fmt canvas.height}\" viewBox=\"0 0 {fmt canvas.width} {fmt canvas.height}\">"
  String.intercalate "\n" ([header] ++ lines ++ annLines ++ ["</svg>"])

end Figures.SVG

namespace Figures

/-- Render this construction as a standalone SVG document. Wrapper so
`c.toSvg` dot-notation resolves; defers to `Figures.SVG.render`. -/
def Construction.toSvg (c : Construction) (canvas : SVG.Canvas := {}) : String :=
  SVG.render c canvas

end Figures
