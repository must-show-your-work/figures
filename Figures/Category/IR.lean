/-
Figures/Category/IR.lean — IR for category-theory commutative diagrams.

A `Diagram` is a multigraph of nodes (objects of a category) and
edges (morphisms), together with optional cells asserting commutativity
of paths. Position-free: positions are assigned by a layout pass
(`Figures.Category.Layout`) before lowering to `Scene Pos2`.

Lives in figures (not in any consumer) so the IR is shared across
backends and the eventual proof-state classifier registry has a target
type that doesn't pull in any consumer-specific code.
-/

import Figures
import Figures.Construction.DSL

namespace Figures.Category

open Figures

/-! ## Label sources

For V1 a label is either a literal string (rendered as plain SVG text)
or a LaTeX source string (V2 will render via tectonic + dvisvgm + cache).
The discriminator is set at DSL elaboration time. -/

inductive Label
  /-- Plain text label, rendered as SVG `<text>`. The `txt` variant
  carries strings the consumer already considers display-ready. -/
  | txt   (content : String)
  /-- LaTeX source — currently rendered as plain text in V1; V2 will
  swap in tectonic rendering with cached SVG fragments. -/
  | latex (source : String)
deriving Repr, Inhabited

/-- The string form a renderer uses when it doesn't know how to do
LaTeX. In V1 both backends fall back to this — V2 will branch on
the `latex` constructor and call the LaTeX backend. -/
def Label.fallbackText : Label → String
  | .txt s   => s
  | .latex s => s


/-! ## Nodes, edges, cells -/

structure Node where
  /-- Stable identifier (DSL ident), used to refer to this node from
  edges and `commutes` paths. -/
  name  : String
  label : Label
deriving Repr, Inhabited

structure Edge where
  source : String
  target : String
  label  : Label
  head   : ArrowHead := .standard
  /-- Suggested bend; the layout pass may override. Positive curves
  to the left of the chord, negative to the right. -/
  bend   : Float := 0
deriving Repr, Inhabited

structure Cell where
  /-- Two or more paths through the graph that the diagram asserts
  are equal. Each path is a sequence of node names; consecutive
  pairs must have an edge between them. -/
  paths : Array (Array String)
deriving Repr, Inhabited


/-! ## Top-level Diagram -/

structure Diagram where
  nodes  : Array Node            := #[]
  edges  : Array Edge            := #[]
  cells  : Array Cell            := #[]
  /-- Optional explicit layout selector. `none` means run the
  classifier registry; otherwise it names a registered layout
  template like `"square"`, `"triangle"`, `"pullback"`, … -/
  layout : Option String         := none
deriving Repr, Inhabited

/-! ## Convenience accessors -/

/-- Find a node by name. -/
def Diagram.node? (d : Diagram) (name : String) : Option Node :=
  d.nodes.find? fun n => n.name == name

/-- Find an edge by source / target. -/
def Diagram.edge? (d : Diagram) (source target : String) : Option Edge :=
  d.edges.find? fun e => e.source == source ∧ e.target == target


/-! ## Conversion from `Figures.Construction.DSL.Construction`

The DSL parses `construction { commutative diagram; node ...; arrow ...; ... }`
into a flat `Construction.Stmt` sequence. This function walks that
sequence and assembles a `Diagram`. Statements that don't belong to
category-diagram mode are ignored (so a mixed geometry-then-category
construction would error elsewhere; we only consume the category bits).

Returns `none` if the construction has no `mode "commutative diagram"`
marker — caller can route to a different processor in that case. -/

def Diagram.fromConstruction (c : Figures.Construction.DSL.Construction) :
    Option Diagram := Id.run do
  let hasMode := c.stmts.any fun s => match s with
    | .mode "commutative diagram" => true
    | _ => false
  unless hasMode do return none
  let mut nodes  : Array Node   := #[]
  let mut edges  : Array Edge   := #[]
  let mut cells  : Array Cell   := #[]
  let mut layout : Option String := none
  for s in c.stmts do
    match s with
    | .node name label =>
      nodes := nodes.push { name := name, label := .latex label }
    | .edge src tgt label head =>
      edges := edges.push { source := src, target := tgt, label := .latex label, head := head }
    | .commutes paths =>
      cells := cells.push { paths := paths }
    | .layoutHint template =>
      layout := some template
    | _ => continue
  return some { nodes := nodes, edges := edges, cells := cells, layout := layout }

end Figures.Category
