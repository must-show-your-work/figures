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
  width  : Float := 1280
  height : Float := 720
  /-- Background fill applied via a full-viewport `<rect>` as the
  first child. Defaults to an aged-legal-pad yellow; set to `"none"`
  to skip the rect and get a transparent background. Without this,
  dark strokes on a dark terminal background are unreadable. -/
  background : String := "#f9e8a0"
  /-- Whether to emit the inline `<style>` block that sets
  font-family / fill / halo for the `.txt`, `.lbl`, `.callout`
  classes. Defaults to `true` for standalone consumers (the
  ProofWidgets InfoView, libresvg rasterization, `IO.println`
  debug) which have no host CSS to fall back to. Hosts that DO
  supply their own CSS for those classes (e.g. the atlas viewer
  which wants editorial theme overrides) pass `inlineStyles := false`
  to get a markup-only SVG; their stylesheet then drives the look. -/
  inlineStyles : Bool := true
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
  -- `currentColor` defers to the host's CSS `color` property so the
  -- figure inverts cleanly between light and dark themes. Backends
  -- that supply a concrete page color (default Canvas background)
  -- still render correctly because browsers resolve `currentColor`
  -- against the enclosing element's computed color.
  strokeColor   : String := "currentColor"
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
    s!"  <circle id=\"{id}\" cx=\"{fmt pos.x}\" cy=\"{fmt pos.y}\" r=\"{s.pointRadius}\" fill=\"currentColor\" />"
  | .segment id a b style =>
    let s := applyStyle style
    s!"  <line id=\"{id}\" x1=\"{fmt a.x}\" y1=\"{fmt a.y}\" x2=\"{fmt b.x}\" y2=\"{fmt b.y}\"{styleAttrs s} />"
  | .ray id a b style =>
    -- Extend ~25% past b in the (a→b) direction; arrowhead marker
    -- (see `render` header's <defs>) caps the open end.
    let s := applyStyle style
    let dx := b.x - a.x
    let dy := b.y - a.y
    let ext : Pos2 := (b.x + dx * 0.25, b.y + dy * 0.25)
    s!"  <line id=\"{id}\" x1=\"{fmt a.x}\" y1=\"{fmt a.y}\" x2=\"{fmt ext.x}\" y2=\"{fmt ext.y}\"{styleAttrs s} marker-end=\"url(#arrow)\" />"
  | .line id a b style =>
    let s := applyStyle style
    let (p, q) := extendToViewport a b canvas.width canvas.height
    s!"  <line id=\"{id}\" x1=\"{fmt p.x}\" y1=\"{fmt p.y}\" x2=\"{fmt q.x}\" y2=\"{fmt q.y}\"{styleAttrs s} />"
  | .circle id center radius style =>
    let s := applyStyle style
    s!"  <circle id=\"{id}\" cx=\"{fmt center.x}\" cy=\"{fmt center.y}\" r=\"{fmt radius}\" fill=\"none\"{styleAttrs s} />"
  | .text id pos content =>
    -- HTML-escape `& < >` so the SVG stays well-formed. Styling is
    -- via the `.txt` CSS class in the `<style>` block (see `render`).
    -- This matches the hand-authored SVGs that render reliably in
    -- lean.nvim's libresvg path; inline `font-family` attributes
    -- silently drop text in some libresvg configurations.
    let escaped := content.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    s!"  <text id=\"{id}\" class=\"txt\" x=\"{fmt pos.x}\" y=\"{fmt pos.y}\">{escaped}</text>"


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
  | .ray _ a b _         =>
    -- Anchor at the arrow tip (slightly past b in (a→b) direction).
    let dx := b.x - a.x
    let dy := b.y - a.y
    (b.x + dx * 0.25, b.y + dy * 0.25)
  | .line _ a b _        =>
    -- Anchor at the entry viewport intersection (typically upper-left
    -- for a downward-sloping line) — standard geometry convention
    -- places the line label at the "less-busy" end of the visible
    -- segment, and entry usually has more empty space than exit.
    let (p, _) := extendToViewport a b canvas.width canvas.height
    let nudgeX := if p.x < canvas.width / 2 then 40 else -40
    (p.x + nudgeX, p.y)
  | .circle _ center _ _ => center
  | .text _ pos _        => pos

private def shapeId : Shape Pos2 → Name
  | .point id _ _      => id
  | .segment id _ _ _  => id
  | .ray id _ _ _      => id
  | .line id _ _ _     => id
  | .circle id _ _ _   => id
  | .text id _ _       => id

private def anchorOf (canvas : Canvas) (shapes : Array (Shape Pos2)) (target : Name) : Option Pos2 :=
  (shapes.find? (fun s => shapeId s == target)).map (shapeAnchor canvas)

private def renderAnnotation (canvas : Canvas) (shapes : Array (Shape Pos2)) (a : Annotation) : Option String :=
  match a with
  | .label target text offset? => do
      let p ← anchorOf canvas shapes target
      let escaped := text.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
      -- Two paths: (1) caller supplied a solved offset → use it; (2)
      -- fallback heuristic — direction from canvas center to anchor.
      let (ox, oy) ← match offset? with
        | some off => some (off.x, off.y)
        | none =>
          let cx := canvas.width / 2
          let cy := canvas.height / 2
          let dx := p.x - cx
          let dy := p.y - cy
          let len := (dx * dx + dy * dy).sqrt
          let standoff : Float := 28
          if len < 1e-9 then some (0, -standoff)
          else some (dx / len * standoff, dy / len * standoff)
      let anchor := if ox >= 0 then "start" else "end"
      let margin : Float := 60
      let raw_x := p.x + ox
      let raw_y := p.y + oy
      let lx := max margin (min (canvas.width  - margin) raw_x)
      let ly := max margin (min (canvas.height - margin) raw_y)
      some s!"  <text class=\"lbl\" text-anchor=\"{anchor}\" x=\"{fmt lx}\" y=\"{fmt ly}\">{escaped}</text>"
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
        [ s!"  <line x1=\"{fmt (p.x + 12)}\" y1=\"{fmt p.y}\" x2=\"{fmt (p.x + 60)}\" y2=\"{fmt p.y}\" stroke=\"currentColor\" stroke-opacity=\"0.55\" stroke-width=\"0.75\" />"
        , s!"  <text class=\"callout\" x=\"{fmt (p.x + 65)}\" y=\"{fmt (p.y + 4)}\">{escaped}</text>" ]


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
            | .ray id a b _        => .ray id a b style
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
  -- CSS style block for text. Uses concrete font-family names instead
  -- of the generic `serif`/`sans-serif` keywords: resvg/libresvg's
  -- fontdb resolves family names exactly and silently drops text when
  -- it can't match `serif` (browsers and most other UAs alias generic
  -- keywords, but libresvg does not). Browsers ignore unknown families
  -- and fall back to the next, so listing the generic as a fallback
  -- keeps the SVG portable.
  let bg := canvas.background
  let halo := "stroke: " ++ bg ++ "; stroke-width: 4px; paint-order: stroke;"
  let styleBlock := if !canvas.inlineStyles then "" else
    "  <style>\n"
    ++ "    .txt { font-family: \"DejaVu Serif\", serif; font-size: 22px; fill: #073642; " ++ halo ++ " }\n"
    ++ "    .lbl { font-family: \"DejaVu Serif\", serif; font-size: 22px; font-style: italic; fill: #073642; " ++ halo ++ " }\n"
    ++ "    .callout { font-family: \"DejaVu Sans\", sans-serif; font-size: 18px; fill: #555; " ++ halo ++ " }\n"
    ++ "  </style>"
  -- Arrowhead marker for rays. SVG marker units are in stroke widths
  -- by default; refX positions the tip at the marker's reference point
  -- so the arrow's apex sits on the ray's end coordinate.
  let arrowDefs :=
    "  <defs>\n"
    ++ "    <marker id=\"arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n"
    ++ "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"currentColor\" />\n"
    ++ "    </marker>\n"
    ++ "  </defs>"
  let bgLines := if canvas.background = "none" then [] else
    [s!"  <rect width=\"100%\" height=\"100%\" fill=\"{canvas.background}\" />"]
  -- Drop the empty styleBlock when inlineStyles is false so the
  -- output doesn't end up with a stray blank line at the top.
  let topMatter := if styleBlock.isEmpty then [header, arrowDefs] else [header, styleBlock, arrowDefs]
  String.intercalate "\n" (topMatter ++ bgLines ++ shapeLines ++ annLines ++ ["</svg>"])


/-! ## Plugin registration -/

end Figures.SVG

namespace Figures

/-- SVG backend for 2D scenes. atlas's `direct_rep` dispatches through
this via `Renderable α String` instance lookup. -/
instance : Renderable (Scene Pos2) String where
  render s := SVG.render s

end Figures
