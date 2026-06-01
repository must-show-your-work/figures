/-
Figures/SVG.lean — SVG backend for `Scene Pos2`.

Walks `Scene.shapes` in order and emits a standalone SVG document.
Positions come from the scene (no layout pass), so the renderer is a
straight serializer. Constraints are ignored at this layer.

Output is a self-contained SVG (xmlns + viewBox + paper-white
background rect) that works in browsers, libresvg-rasterizing widgets,
and `IO.println` debug.

Registers as `instance : Renderable (Scene Pos2) String` so atlas's
`direct_rep` (and any other consumer that dispatches via
`Renderable`) can pick this backend up by type.
-/

import Figures

namespace Figures.SVG

open Figures


/-! ## Canvas / viewport -/

structure Canvas where
  width  : Float := 480
  height : Float := 480
  /-- Background fill applied via a full-viewport `<rect>` as the
  first child. Defaults to Solarized base3 (paper-white); set to
  `"none"` to skip the rect and get a transparent background. Without
  this, dark strokes on a dark terminal background are unreadable. -/
  background : String := "#fdf6e3"
deriving Repr, Inhabited


/-! ## Float formatting -/

/-- Trim Lean's default 6-decimal Float printing for cleaner SVG.
`String.dropEndWhile` and `String.dropEnd` return a `String.Slice`;
we `.toString` it back at each step so the rest of the renderer stays
in `String` land. -/
private def fmt (x : Float) : String :=
  let s := toString x
  if s.contains '.' then
    let trimmed := (s.dropEndWhile (· == '0')).toString
    if trimmed.endsWith "." then (trimmed.dropEnd 1).toString else trimmed
  else s


/-! ## Style → SVG attribute computation

Each attribute is computed once with style-aware defaults so the
output never contains duplicate attributes (libresvg rejects those
with `resvg_parse_tree_from_data failed: 6`). -/

/-- Map a `Style` (from a `.highlight` annotation) to a per-shape
record of attribute overrides. -/
private structure ShapeStyle where
  strokeColor   : String := "black"
  strokeWidth   : String := "1.5"
  strokeDash    : Option String := none  -- e.g. "5,3"
  strokeOpacity : Option String := none  -- e.g. "0.35"
  pointRadius   : String := "4"

private def applyStyle (s : Style) : ShapeStyle :=
  match s with
  | .default => {}
  | .dashed  => { strokeDash := some "5,3" }
  | .dotted  => { strokeDash := some "1,2" }
  | .bold    => { strokeWidth := "3", pointRadius := "6" }
  | .faint   => { strokeOpacity := some "0.35" }
  | .color c => { strokeColor := c }

/-- Render the style as SVG attribute fragments. Each attribute
appears at most once. -/
private def styleAttrs (s : ShapeStyle) : String :=
  s!" stroke=\"{s.strokeColor}\" stroke-width=\"{s.strokeWidth}\""
    ++ (match s.strokeDash with
        | some d => s!" stroke-dasharray=\"{d}\""
        | none   => "")
    ++ (match s.strokeOpacity with
        | some o => s!" stroke-opacity=\"{o}\""
        | none   => "")


/-! ## Line viewport extension

A geometric line is infinite. The IR records two reference points
that determine the line; the renderer clips against the canvas
viewport so the rendered line exits both edges. This is the standard
2D Liang-Barsky line-clipping geometry. -/

/-- Extend the line through `a` and `b` to the boundary of the
viewport `[0, w] × [0, h]`. Returns the two boundary intersection
points. Handles vertical and horizontal lines as special cases to
avoid division by ~0. -/
private def extendToViewport (a b : Pos2) (w h : Float) : Pos2 × Pos2 :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  if Float.abs dx < 1e-9 then
    ((a.x, 0), (a.x, h))
  else if Float.abs dy < 1e-9 then
    ((0, a.y), (w, a.y))
  else
    -- Parametric form: (a.x + t·dx, a.y + t·dy).
    -- Clip interval [tEnter, tExit] = intersection of the two
    -- axis-aligned clip ranges (Liang-Barsky).
    let t1 := -a.x / dx
    let t2 := (w - a.x) / dx
    let t3 := -a.y / dy
    let t4 := (h - a.y) / dy
    let tEnter := max (min t1 t2) (min t3 t4)
    let tExit  := min (max t1 t2) (max t3 t4)
    let p (t : Float) : Pos2 := (a.x + t * dx, a.y + t * dy)
    (p tEnter, p tExit)


/-! ## Shape serialization

`renderShape` is parameterized by the canvas so `.line` can extend
to the viewport. Other shape kinds ignore the canvas. -/

private def renderShape (canvas : Canvas) : Shape Pos2 → String
  | .point id pos style =>
    let s := applyStyle style
    s!"  <circle id=\"{id}\" cx=\"{fmt pos.x}\" cy=\"{fmt pos.y}\" r=\"{s.pointRadius}\" fill=\"black\" />"
  | .segment id a b style =>
    let s := applyStyle style
    s!"  <line id=\"{id}\" x1=\"{fmt a.x}\" y1=\"{fmt a.y}\" x2=\"{fmt b.x}\" y2=\"{fmt b.y}\"{styleAttrs s} />"
  | .line id a b style =>
    let s := applyStyle style
    let (p, q) := extendToViewport a b canvas.width canvas.height
    s!"  <line id=\"{id}\" x1=\"{fmt p.x}\" y1=\"{fmt p.y}\" x2=\"{fmt q.x}\" y2=\"{fmt q.y}\"{styleAttrs s} />"
  | .circle id center radius style =>
    let s := applyStyle style
    s!"  <circle id=\"{id}\" cx=\"{fmt center.x}\" cy=\"{fmt center.y}\" r=\"{fmt radius}\" fill=\"none\"{styleAttrs s} />"
  | .text id pos content =>
    -- HTML-escape the content's `& < >` so the SVG stays well-formed.
    -- Explicit `fill` is load-bearing: libresvg renders text as
    -- invisible without it (the SVG spec defaults to black, but
    -- rasterizers vary on whether they honor that default).
    let escaped := content.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    s!"  <text id=\"{id}\" x=\"{fmt pos.x}\" y=\"{fmt pos.y}\" font-family=\"serif\" font-size=\"14\" fill=\"#073642\">{escaped}</text>"


/-! ## Annotations

Annotations may reference shapes by name; look up the anchor position
from the scene's shape list. -/

/-- Anchor point for an annotation referencing the given shape.
Points / circles / text anchor at their own position; segments at
their midpoint; lines anchor at the right viewport exit (slightly
nudged in) so the label doesn't collide with whatever else lives at
the line's midpoint. -/
private def shapeAnchor (canvas : Canvas) : Shape Pos2 → Pos2
  | .point _ pos _       => pos
  | .segment _ a b _     => ((a.x + b.x) / 2, (a.y + b.y) / 2)
  | .line _ a b _        =>
    let (_, q) := extendToViewport a b canvas.width canvas.height
    -- Nudge inward so the label stays on-canvas regardless of which
    -- edge the line exited.
    let nudgeX := if q.x > canvas.width / 2 then -20 else 20
    (q.x + nudgeX, q.y)
  | .circle _ center _ _ => center
  | .text _ pos _        => pos

private def shapeId : Shape Pos2 → Name
  | .point id _ _      => id
  | .segment id _ _ _  => id
  | .line id _ _ _     => id
  | .circle id _ _ _   => id
  | .text id _ _       => id

private def anchorOf (canvas : Canvas) (shapes : Array (Shape Pos2)) (target : Name) : Option Pos2 :=
  (shapes.find? (fun s => shapeId s == target)).map (shapeAnchor canvas)

private def renderAnnotation (canvas : Canvas) (shapes : Array (Shape Pos2)) (a : Annotation) : Option String :=
  match a with
  | .label target text => do
      let p ← anchorOf canvas shapes target
      let escaped := text.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
      -- `fill` is load-bearing for libresvg (see `renderShape` for `.text`).
      some s!"  <text x=\"{fmt (p.x + 8)}\" y=\"{fmt (p.y - 8)}\" font-family=\"serif\" font-size=\"14\" font-style=\"italic\" fill=\"#073642\">{escaped}</text>"
  | .highlight _ _ =>
      -- Highlights are realized by post-processing shapes (see `applyHighlights` below).
      none
  | .angleMark _ _ _ _ =>
      -- TODO: arc at the angle vertex. Out of scope for MVP.
      none
  | .callout target text => do
      let p ← anchorOf canvas shapes target
      let escaped := text.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
      some <| String.intercalate "\n"
        [ s!"  <line x1=\"{fmt (p.x + 12)}\" y1=\"{fmt p.y}\" x2=\"{fmt (p.x + 60)}\" y2=\"{fmt p.y}\" stroke=\"#555\" stroke-width=\"0.75\" />"
        , s!"  <text x=\"{fmt (p.x + 65)}\" y=\"{fmt (p.y + 4)}\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#555\">{escaped}</text>" ]


/-! ## Highlight pass

A `.highlight target style` annotation re-styles the named shape in
place. Implemented as a pre-render pass that overrides each matching
shape's `style` field. Last-write-wins on the same name. -/

private def applyHighlights (shapes : Array (Shape Pos2)) (anns : Array Annotation) : Array (Shape Pos2) :=
  anns.foldl
    (init := shapes)
    (fun acc a => match a with
      | .highlight target style =>
        acc.map fun s =>
          if shapeId s == target then
            match s with
            | .point id pos _      => .point id pos style
            | .segment id a b _    => .segment id a b style
            | .line id a b _       => .line id a b style
            | .circle id c r _     => .circle id c r style
            | other                => other
          else s
      | _ => acc)


/-! ## Top-level render -/

/-- Render a 2D scene as a standalone SVG document. Standalone so the
output is browser-openable, libresvg-rasterizable (via atlas's
`SvgParser`), and `IO.println`-friendly. -/
def render (s : Scene Pos2) (canvas : Canvas := {}) : String :=
  let styledShapes := applyHighlights s.shapes s.annotations
  let shapeLines := styledShapes.toList.map (renderShape canvas)
  let annLines := s.annotations.toList.filterMap (renderAnnotation canvas styledShapes)
  let header :=
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{fmt canvas.width}\" height=\"{fmt canvas.height}\" viewBox=\"0 0 {fmt canvas.width} {fmt canvas.height}\">"
  let bgLines := if canvas.background = "none" then [] else
    [s!"  <rect width=\"100%\" height=\"100%\" fill=\"{canvas.background}\" />"]
  String.intercalate "\n" ([header] ++ bgLines ++ shapeLines ++ annLines ++ ["</svg>"])


/-! ## Plugin registration -/

end Figures.SVG

namespace Figures

/-- SVG backend for 2D scenes. atlas's `direct_rep` dispatches through
this via `Renderable α String` instance lookup. -/
instance : Renderable (Scene Pos2) String where
  render s := SVG.render s

end Figures
