/-
Geometry/Construction.lean — IR for geometric figures + proof-time
extensions.

MVP scope: data structures only. No parser, no renderer, no
constraint solver. The IR is the substrate the rest of the pipeline
plugs into:

```
              parse                         backends
input DSL  ─────────►  Construction (IR)  ───────────►  SVG  (in-editor)
                                            │           GGB  (atlas web viewer)
                                            └────►  Construction.toSource
                                                    (debug / round-trip)
```

The input DSL is the source the user writes inside a `construction`
tactic block — the canonical form is:

```
figure := by construction
  exists A B C : Point
  exists L : Line
  assert distinct A B C
  …
```

The `construction` tactic enters a state-monad over the IR that
accumulates `Step`s; the parser is a follow-up. `toSource` is its
inverse, useful for `#eval` checks and diff-friendly artifacts.

Design notes:
- IR is **purely symbolic**: objects are stable string names referring
  back to earlier introductions; no coordinates are stored.
- IR is **inconsistency-tolerant**: contradictory constraints are not
  rejected. A renderer / solver downstream may produce a garbage
  diagram, but that's a downstream concern. See pasch.lean L66-69 for
  the rationale.
- IR has **three layers of additions** (matching the surface syntax
  in pasch.lean):
  1. `base` — the initial figure as described by the theorem statement
     (`figure := by construction …`).
  2. `extensions` — proof-time additions (`figure := auxillary …`
     inside a `clearly` block). Ordered; renderers may walk this list
     to show "diagram state at proof step K".
  3. `annotations` — call-outs / labels / highlights. Do not introduce
     objects; reference existing ones.

Surface DSL (`construction`, `exists`, `construct`, `assert`, …) is not
in this file — that's a follow-up. This file only models the data the
DSL elaborates into.

Self-contained: no Mathlib, no Lean.Meta. The IR is plain Lean data,
so it can lift to a standalone library if/when we extract it.
-/

namespace Figures

/-! ## Object kinds and names -/

/-- The kind of object an `exist` step introduces. Open via `.other`
so the IR doesn't have to be extended in lock-step with the geometry
library's vocabulary. -/
inductive Kind
  | point
  | line
  | circle
  | segment
  | ray
  | angle
  /-- A real-valued scalar (length, ratio, etc.). -/
  | scalar
  /-- Escape hatch for kinds we haven't named yet. -/
  | other (name : String)
deriving Repr, DecidableEq, Inhabited

/-- Object identity is a stable string. Two steps that introduce
"A" refer to the same object; downstream stages do alpha-renaming
if disambiguation is needed. Keeping this a `String` (not a fresh
`Nat`) lets pseudo-IR examples read like the textbook. -/
abbrev Name := String


/-! ## Expressions

`Expr` is the right-hand side of a `construct` and the body of an
`assert`. We use a generic `name`/`app` shape rather than a closed
inductive of operations so the IR doesn't gate on us extending its
case list every time the surface DSL grows a new primitive.

Examples mapping the pasch.lean pseudo:
- `segment A B`             → `app "segment" [name "A", name "B"]`
- `¬(collinear A B C)`      → `app "¬" [app "collinear" [name "A", name "B", name "C"]]`
- `L intersects segment AB` → `app "intersects" [name "L", app "segment" [name "A", name "B"]]`
- `segment AB = segment BC` → `app "=" [<segment AB>, <segment BC>]`
-/

inductive Expr
  /-- Reference a previously-introduced object by name. -/
  | name (n : Name)
  /-- Function-style application: `op(args…)`. `op` is the name of
  the operator (a string, deliberately open). Arity is not validated
  by the IR — that's a renderer / solver concern. -/
  | app (op : String) (args : List Expr)
  /-- Numeric literal (for things like "circle of radius 1"). -/
  | num (val : Float)
deriving Repr, Inhabited

namespace Expr

/-- Convenience for the very common no-args case. -/
def of (n : Name) : Expr := .name n

/-- Convenience for the very common one/two-arg cases — keep the
pseudo-IR readable. -/
def app1 (op : String) (a : Expr) : Expr := .app op [a]
def app2 (op : String) (a b : Expr) : Expr := .app op [a, b]
def app3 (op : String) (a b c : Expr) : Expr := .app op [a, b, c]

end Expr


/-! ## Steps

A `Step` is one line of the construction. Three flavors only,
matching the pasch.lean surface:

- `exist name kind`    — introduce a free object.
- `construct name rhs` — derive a named object from existing ones.
- `assert claim`       — pose a constraint over existing objects.
                         The claim may be contradictory; the IR
                         doesn't care.
-/

inductive Step
  | exist (name : Name) (kind : Kind)
  | construct (name : Name) (rhs : Expr)
  | assert (claim : Expr)
deriving Repr, Inhabited


/-! ## Annotations

Annotations affect rendering only — labels, highlights, angle marks,
callouts. They reference existing objects but introduce none.
-/

/-- Visual style hints for an annotation. Renderer-defined how each
is interpreted; the IR just carries the requested style. -/
inductive Style
  | default
  | dashed
  | dotted
  | bold
  | faint
  /-- Hex color or named CSS color, e.g. `"#ff0000"` or `"crimson"`. -/
  | color (c : String)
deriving Repr, Inhabited

inductive Annotation
  /-- Place a text label near `target`. -/
  | label (target : Name) (text : String)
  /-- Apply a visual style to `target` (line gets dashed, point gets
  highlighted, etc.). -/
  | highlight (target : Name) (style : Style)
  /-- Draw an angle-mark arc at the angle `(a, vertex, c)` (vertex in
  the middle, matching the standard `∠abc` reading). Optional name
  appears next to the arc. -/
  | angleMark (a vertex c : Name) (name : Option String := none)
  /-- Callout box / arrow with `text` pointing at `target`. -/
  | callout (target : Name) (text : String)
deriving Repr, Inhabited


/-! ## Construction

The full IR record. `base` is what the theorem statement gives us;
`extensions` collects auxiliary constructions added inside `clearly`
or other sub-proof blocks (see pasch.lean L86); `annotations` is
flat — they're not ordered relative to construction steps because
they're rendering-time decorations, not steps in the construction.
-/

structure Construction where
  /-- The initial figure as described by the theorem statement. -/
  base : List Step := []
  /-- Proof-time additions. Order matters — renderers may want to
  show "diagram at step K of the proof". -/
  extensions : List Step := []
  /-- Decorations applied to objects mentioned in `base` or
  `extensions`. -/
  annotations : List Annotation := []
deriving Repr, Inhabited


/-! ## Source pretty-printer

Renders an IR record back into the (still-unnamed) input DSL syntax.
This is the inverse of the eventual `figure := by …` parser: the
parser consumes source, produces a `Construction`; this prints a
`Construction` back as source. Useful as a `#eval`-able sanity check
and for diff-friendly artifacts. Not load-bearing for any renderer
(SVG / GeoGebra backends consume the IR directly).
-/

namespace Expr

partial def toSource : Expr → String
  | .name n => n
  | .num x  => toString x
  | .app op args =>
    let rendered := args.map toSource
    -- Prefix-style printing keeps things uniform; readers can
    -- mentally rewrite `app "=" [x, y]` as `x = y` if they like.
    s!"{op}({String.intercalate ", " rendered})"

end Expr

namespace Style

def toSource : Style → String
  | .default => "default"
  | .dashed  => "dashed"
  | .dotted  => "dotted"
  | .bold    => "bold"
  | .faint   => "faint"
  | .color c => s!"color({c})"

end Style

namespace Step

def kindToSource : Kind → String
  | .point => "Point"
  | .line => "Line"
  | .circle => "Circle"
  | .segment => "Segment"
  | .ray => "Ray"
  | .angle => "Angle"
  | .scalar => "Scalar"
  | .other s => s

def toSource : Step → String
  | .exist n k     => s!"exists {n} : {kindToSource k}"
  | .construct n r => s!"construct {n} := {r.toSource}"
  | .assert c      => s!"assert {c.toSource}"

end Step

namespace Annotation

def toSource : Annotation → String
  | .label t txt           => s!"label {t} {repr txt}"
  | .highlight t s         => s!"highlight {t} {s.toSource}"
  | .angleMark a v c name  =>
    let suffix := match name with | none => "" | some n => s!" as {n}"
    s!"angleMark {a} {v} {c}{suffix}"
  | .callout t txt         => s!"callout {t} {repr txt}"

end Annotation

namespace Construction

/-- Source-form text dump of the whole construction. Sections show
the layer of each step. -/
def toSource (c : Construction) : String :=
  let header (h : String) := s!"-- {h}"
  let bullet (s : String) := s!"  {s}"
  let baseLines := header "base" :: c.base.map (bullet ∘ Step.toSource)
  let extLines :=
    if c.extensions.isEmpty then [] else
      header "extensions" :: c.extensions.map (bullet ∘ Step.toSource)
  let annLines :=
    if c.annotations.isEmpty then [] else
      header "annotations" :: c.annotations.map (bullet ∘ Annotation.toSource)
  String.intercalate "\n" (baseLines ++ extLines ++ annLines)

end Construction


end Figures
