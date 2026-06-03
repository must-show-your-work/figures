/-
Figures.lean — core IR + plugin API for the figures library.

A `Scene` is a concrete drawable: a flat list of `Shape`s with
positions, optional `Annotation`s, and optional `Constraint` metadata.
No relational logic, no constraint solving — that's a frontend's job.
Backends walk the shapes and emit output (SVG, GeoGebra, …) via the
`Renderable` typeclass.

Positions are polymorphic in `P` so the same IR can express 2D / 3D /
projected / colorspace scenes. Standard backends pick the dimensions
they support (the bundled SVG backend targets `Scene Pos2`).

What's IN the IR:
  - Shapes with concrete positions
  - Style hints
  - Annotations (labels, highlights, …)
  - Optional Constraint metadata, opaque structural data backends may
    consume if they care (the GeoGebra backend wants this; SVG ignores)

What's NOT in the IR:
  - Domain concepts (betweenness, incidence, perpendicularity, …)
  - Constraint solving
  - Symbolic objects without positions

Domain concepts live in FRONTENDS (e.g. giyf's geometric DSL) which
compile down to a `Scene` whose positions already honor the
constraints. figures stays geometry-agnostic.
-/

namespace Figures

/-! ## Position types -/

/-- A 2D position. -/
abbrev Pos2 := Float × Float

/-- A 3D position. -/
abbrev Pos3 := Float × Float × Float

namespace Pos2

/-- x-component. -/
def x (p : Pos2) : Float := p.1
/-- y-component. -/
def y (p : Pos2) : Float := p.2
/-- Construct from x, y. -/
def mk (x y : Float) : Pos2 := (x, y)

end Pos2


/-! ## Identifiers, styles, annotations -/

/-- Stable string ID for a shape. Used by annotations / future
backends to refer to a specific shape after rendering. -/
abbrev Name := String

inductive Style
  | default
  /-- Dashed stroke. -/
  | dashed
  /-- Dotted stroke. -/
  | dotted
  /-- Thick stroke. -/
  | bold
  /-- Reduced opacity. -/
  | faint
  /-- Custom stroke color (hex `#rrggbb` or named CSS color). -/
  | color (c : String)
deriving Repr, Inhabited

inductive Annotation
  /-- Place a text label near `target`. The optional `offset` is the
  pre-computed displacement from `target`'s anchor; when present, the
  backend uses it verbatim and skips its own placement heuristic.
  When `none`, the backend applies a default standoff. -/
  | label (target : Name) (text : String) (offset : Option Pos2 := none)
  /-- Apply a visual style to `target`. -/
  | highlight (target : Name) (style : Style)
  /-- Draw an angle-mark arc at the angle `(a, vertex, c)` (vertex
  in the middle, matching the `∠abc` reading). -/
  | angleMark (a vertex c : Name) (name : Option String := none)
  /-- Callout box / arrow with `text` pointing at `target`. -/
  | callout (target : Name) (text : String)
deriving Repr, Inhabited


/-! ## Shapes -/

/-- Drawable primitives. `P` is the position type; for 2D figures
this is `Pos2`. -/
inductive Shape (P : Type)
  | point   (id : Name) (pos : P)                          (style : Style := .default)
  | segment (id : Name) (a b : P)                          (style : Style := .default)
  /-- A ray starts at `a`, passes through `b`, and extends past `b`
  with an arrowhead. Backends draw the visible portion from `a` to
  past `b` (the "open" end). -/
  | ray     (id : Name) (a b : P)                          (style : Style := .default)
  /-- A line is defined by two reference points; backends extend
  through the canvas at render time. Vector form (point + direction)
  is a future addition. -/
  | line    (id : Name) (a b : P)                          (style : Style := .default)
  | circle  (id : Name) (center : P) (radius : Float)      (style : Style := .default)
  | text    (id : Name) (pos : P) (content : String)
deriving Repr, Inhabited


/-! ## Constraint metadata

Opaque structural data backends can consume if they want to expose
the geometric intent (e.g. a GeoGebra emitter wires up draggable
points respecting `between A X B`). Default SVG backend ignores.
Frontends populate this; figures itself has no opinion about what
operator strings mean. -/

inductive ConstraintExpr
  /-- Reference a shape by ID. -/
  | name (n : Name)
  /-- Function-style application. -/
  | app (op : String) (args : List ConstraintExpr)
  /-- Numeric literal. -/
  | num (val : Float)
deriving Repr, Inhabited

structure Constraint where
  claim : ConstraintExpr
  /-- Optional human-readable label, used for tooltips / debug
  output. Empty string = no label. -/
  description : String := ""
deriving Repr, Inhabited


/-! ## Scene

The top-level IR record. Backends consume a `Scene P` and emit
output. The `P` parameter is polymorphic so the same IR shape works
for 2D / 3D / etc. -/

structure Scene (P : Type) where
  shapes      : Array (Shape P) := #[]
  annotations : Array Annotation := #[]
  /-- Optional constraint metadata. Default backends ignore;
  domain-aware backends (GeoGebra) may consume. -/
  constraints : Array Constraint := #[]
deriving Repr, Inhabited


/-! ## Plugin API -/

/-- The backend plugin interface. A backend is an instance
`Renderable α out` that takes an `α` (typically a `Scene P`) and
produces an `out` (SVG string, GeoGebra script, EWM figure …).

Frontends produce `α`s; backends consume them. atlas's `direct_rep`
field elaborates its term and dispatches via this typeclass.

Standard backend: `instance : Renderable (Scene Pos2) String` for
SVG output, defined in `Figures.SVG`. -/
class Renderable (α : Type) (out : Type) where
  render : α → out

end Figures
