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

end Figures.Category
